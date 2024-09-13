use anyhow::Result;
use std::{collections::HashMap, convert::TryInto};
use anyhow::anyhow;
use lazy_static::lazy_static;
use solana_sdk::{program_pack::Pack, pubkey, pubkey::Pubkey};
use spl_token_swap::curve::base::SwapCurve;
use spl_token_swap::{state::SwapV1};
use anchor_lang::AccountDeserialize;
use spl_token_2022::extension::transfer_fee::TransferFeeConfig;
use std::sync::atomic::{AtomicI64, AtomicU64};
use std::sync::Arc;
use anyhow::Context;
use jupiter_amm_interface::{
    try_get_account_data, AccountMap, Amm, AmmContext, KeyedAccount, Quote, QuoteParams, Swap,
    SwapAndAccountMetas, SwapParams,
};

use std::str::FromStr;
pub struct SplTokenSwapAmm {
    key: Pubkey,
    label: String,
    state: SwapV1,
    reserve_mints: [Pubkey; 2],
    reserves: [u128; 2],
    program_id: Pubkey,
}

impl SplTokenSwapAmm {
    fn get_authority(&self) -> Pubkey {
        Pubkey::find_program_address(&[&self.key.to_bytes()], &self.program_id).0
    }
}

impl Clone for SplTokenSwapAmm {
    fn clone(&self) -> Self {
        SplTokenSwapAmm {
            key: self.key,
            label: self.label.clone(),
            state: SwapV1 {
                is_initialized: self.state.is_initialized,
                bump_seed: self.state.bump_seed,
                token_program_id: self.state.token_program_id,
                token_a: self.state.token_a,
                token_b: self.state.token_b,
                pool_mint: self.state.pool_mint,
                token_a_mint: self.state.token_a_mint,
                token_b_mint: self.state.token_b_mint,
                pool_fee_account: self.state.pool_fee_account,
                fees: self.state.fees.clone(),
                swap_curve: SwapCurve {
                    curve_type: self.state.swap_curve.curve_type,
                    calculator: self.state.swap_curve.calculator.clone(),
                },
            },
            reserve_mints: self.reserve_mints,
            program_id: self.program_id,
            reserves: self.reserves,
        }
    }
}

pub fn try_deserialize_unchecked_from_bytes<T: AccountDeserialize>(data: &[u8]) -> Result<T> {
    T::try_deserialize(&mut data.as_ref())
        .map_err(|e| anyhow!("Failed to deserialize account: {}", e))
}
pub fn try_deserialize_unchecked_from_bytes_zc(input: &[u8]) -> Result<PoolState> {
    if input.is_empty() {
        return Err(anyhow::anyhow!("Input data is empty"));
    }
    let pool_state = unsafe {
        let pool_state_ptr = input[8..].as_ptr() as *const PoolState;
        std::ptr::read_unaligned(pool_state_ptr)
    };
    Ok(pool_state)
}
use spl_token_2022::extension::BaseStateWithExtensions;
#[derive(Clone, Debug, Default)]
pub struct TokenMintsWithTokenPrograms {
    pub token_0_mint: Pubkey,
    pub token_1_mint: Pubkey,
    pub token_0_program: Pubkey,
    pub token_1_program: Pubkey,
    pub account_map: AccountMap
}

impl AsRef<TokenMintsWithTokenPrograms> for TokenMintsWithTokenPrograms {
    fn as_ref(&self) -> &TokenMintsWithTokenPrograms {
        self
    }
}
use spl_token_2022::extension::StateWithExtensions;
use spl_token_2022::state::Mint;
impl TokenMintsWithTokenPrograms {
    pub fn context(&self, msg: &str) -> Result<&Self> {
        Ok(self)
    }
    pub fn new(
        account_map: &AccountMap,
        token_0_mint: &Pubkey,
        token_1_mint: &Pubkey,
    ) -> Self {
        let token_0_program = account_map.get(token_0_mint)
            .map(|acc| acc.owner)
            .unwrap_or(spl_token::id());
        let token_1_program = account_map.get(token_1_mint)
            .map(|acc| acc.owner)
            .unwrap_or(spl_token::id());
        Self {
            token_0_mint: *token_0_mint,
            token_1_mint: *token_1_mint,
            token_0_program,
            token_1_program,
            account_map: account_map.clone()
        }
    }

    pub fn mints(&self) -> (StateWithExtensions<Mint>, StateWithExtensions<Mint>) {
        let token_0_mint_account = self.account_map.get(&self.token_0_mint)
            .expect("Token 0 mint account not found");
        let token_1_mint_account = self.account_map.get(&self.token_1_mint)
            .expect("Token 1 mint account not found");
        
        let token_0_mint = StateWithExtensions::<Mint>::unpack(&token_0_mint_account.data)
            .expect("Failed to unpack token 0 mint");
        let token_1_mint = StateWithExtensions::<Mint>::unpack(&token_1_mint_account.data)
            .expect("Failed to unpack token 1 mint");
        
        (token_0_mint, token_1_mint)
    }

    pub fn programs(&self) -> (&Pubkey, &Pubkey) {
        (&self.token_0_program, &self.token_1_program)
    }
}

use raydium_cp_swap::{
    states::{AmmConfig, PoolState, PoolStatusBitIndex},
    AUTH_SEED,
};
#[derive(Clone, Default)]
pub struct Fomo3dCpAmm {
    pub key: Pubkey,
    pub pool_state: PoolState,
    pub amm_config: Option<AmmConfig>,
    pub vault_0_amount: Option<u64>,
    pub vault_1_amount: Option<u64>,
    pub token_mints_and_token_programs: TokenMintsWithTokenPrograms,
    pub epoch: Arc<AtomicU64>,
    pub timestamp: Arc<AtomicI64>,
}
impl Fomo3dCpAmm {
    pub fn from_keyed_account(keyed_account: &KeyedAccount, amm_context: &AmmContext) -> Result<Self> {
        let data = &keyed_account.account.data[8..]; // Skip 8-byte discriminator
        
        if data.len() < std::mem::size_of::<PoolState>() {
            return Err(anyhow!("Account data is too small for PoolState"));
        }

        let pool_state = unsafe {
            let pool_state_ptr = data.as_ptr() as *const PoolState;
            std::ptr::read_unaligned(pool_state_ptr)
        };

        Ok(Self {
            key: keyed_account.key,
            pool_state,
            amm_config: None, // This will be populated later in the update method
            vault_0_amount: None, // This will be populated later in the update method
            vault_1_amount: None, // This will be populated later in the update method
            token_mints_and_token_programs: TokenMintsWithTokenPrograms::default(),
            epoch: amm_context.clock_ref.epoch.clone(),
            timestamp: amm_context.clock_ref.unix_timestamp.clone(),
        })
    }
    fn get_authority(&self) -> Pubkey {
        let (authority, __bump) = Pubkey::find_program_address(&[AUTH_SEED.as_bytes()], &Pubkey::from_str("CVF4q3yFpyQwV8DLDiJ9Ew6FFLE1vr5ToRzsXYQTaNrj").unwrap());
        authority
    }
}

use anchor_lang::ToAccountMetas;

pub struct RaydiumCpSwap {
    pub swap_program: Pubkey,
    pub payer: Pubkey,
    pub authority: Pubkey,
    pub amm_config: Pubkey,
    pub pool_state: Pubkey,
    pub input_token_account: Pubkey,
    pub output_token_account: Pubkey,
    pub input_vault: Pubkey,
    pub output_vault: Pubkey,
    pub input_token_program: Pubkey,
    pub output_token_program: Pubkey,
    pub input_token_mint: Pubkey,
    pub output_token_mint: Pubkey,
    pub observation_state: Pubkey,
}
pub struct Fees {
    token_0_lp_rate: u64,
    token_1_lp_rate: u64,
    token_0_creator_rate: u64,
    token_1_creator_rate: u64,
    protocol_fee_rate: u64,
    fund_fee_rate: u64,
}

impl Fees {
    pub fn new(
        token_0_lp_rate: u64,
        token_1_lp_rate: u64,
        token_0_creator_rate: u64,
        token_1_creator_rate: u64,
        protocol_fee_rate: u64,
        fund_fee_rate: u64,
    ) -> Self {
        Self {
            token_0_lp_rate,
            token_1_lp_rate,
            token_0_creator_rate,
            token_1_creator_rate,
            protocol_fee_rate,
            fund_fee_rate,
        }
    }
}
pub struct SwapAccs {
    pub swap_program: Pubkey,
    pub payer: Pubkey,
    pub authority: Pubkey,
    pub amm_config: Pubkey,
    pub pool_state: Pubkey,
    pub input_token_account: Pubkey,
    pub output_token_account: Pubkey,
    pub input_vault: Pubkey,
    pub output_vault: Pubkey,
    pub input_token_program: Pubkey,
    pub output_token_program: Pubkey,
    pub input_token_mint: Pubkey,
    pub output_token_mint: Pubkey,
    pub observation_state: Pubkey,
}
use anchor_lang::prelude::AccountMeta;
impl ToAccountMetas for SwapAccs {
    fn to_account_metas(&self, _is_signer: Option<bool>) -> Vec<AccountMeta> {
        vec![
            AccountMeta::new_readonly(self.swap_program, false),
            AccountMeta::new(self.payer, true),
            AccountMeta::new_readonly(self.authority, false),
            AccountMeta::new_readonly(self.amm_config, false),
            AccountMeta::new(self.pool_state, false),
            AccountMeta::new(self.input_token_account, false),
            AccountMeta::new(self.output_token_account, false),
            AccountMeta::new(self.input_vault, false),
            AccountMeta::new(self.output_vault, false),
            AccountMeta::new_readonly(self.input_token_program, false),
            AccountMeta::new_readonly(self.output_token_program, false),
            AccountMeta::new_readonly(self.input_token_mint, false),
            AccountMeta::new_readonly(self.output_token_mint, false),
            AccountMeta::new(self.observation_state, false),
        ]
    }
}
impl SwapAccs {
    pub fn new(swap: &RaydiumCpSwap) -> Self {
        Self {
            swap_program: Pubkey::from_str("CVF4q3yFpyQwV8DLDiJ9Ew6FFLE1vr5ToRzsXYQTaNrj").unwrap(),
            payer: swap.payer,
            authority: swap.authority,
            amm_config: swap.amm_config,
            pool_state: swap.pool_state,
            input_token_account: swap.input_token_account,
            output_token_account: swap.output_token_account,
            input_vault: swap.input_vault,
            output_vault: swap.output_vault,
            input_token_program: swap.input_token_program,
            output_token_program: swap.output_token_program,
            input_token_mint: swap.input_token_mint,
            output_token_mint: swap.output_token_mint,
            observation_state: swap.observation_state,
        }
    }
}

pub struct ConstantProduct {
    fees: Fees,
    allow_zero_trade_amount: bool,
}

impl ConstantProduct {
    pub fn new(fees: Fees, allow_zero_trade_amount: bool) -> Self {
        Self {
            fees,
            allow_zero_trade_amount,
        }
    }

}

pub struct SwapResult {
    pub new_source_amount: u128,
    pub new_destination_amount: u128,
    pub amount_swapped: u128,
    pub trade_fee: u128,
    pub owner_fee: u128,
}


impl Amm for Fomo3dCpAmm {
   
    fn from_keyed_account(keyed_account: &KeyedAccount, amm_context: &AmmContext) -> Result<Self> {
        let pool_state = try_deserialize_unchecked_from_bytes_zc(&keyed_account.account.data)?;

        Ok(Self {
            key: keyed_account.key,
            pool_state,
            amm_config: None,
            vault_0_amount: None,
            vault_1_amount: None,
            token_mints_and_token_programs: TokenMintsWithTokenPrograms::default(),
            epoch: amm_context.clock_ref.epoch.clone(),
            timestamp: amm_context.clock_ref.unix_timestamp.clone(),
        })
    }

    fn label(&self) -> String {
        "Fomo3d CP".into()
    }

    fn program_id(&self) -> Pubkey {
        Pubkey::from_str("CVF4q3yFpyQwV8DLDiJ9Ew6FFLE1vr5ToRzsXYQTaNrj").unwrap()
    }

    fn key(&self) -> Pubkey {
        self.key
    }

    fn get_reserve_mints(&self) -> Vec<Pubkey> {
        vec![self.pool_state.token_0_mint, self.pool_state.token_1_mint]
    }

    fn get_accounts_to_update(&self) -> Vec<Pubkey> {
        let mut keys = vec![
            self.key,
            self.pool_state.token_0_vault,
            self.pool_state.token_1_vault,
            self.pool_state.amm_config,
        ];
        keys.extend([self.pool_state.token_0_mint, self.pool_state.token_1_mint]);
        keys
    }

    fn update(&mut self, account_map: &AccountMap) -> Result<()> {
        let pool_state_data = try_get_account_data(account_map, &self.key)?;
        self.pool_state = unsafe {
            let pool_state_ptr = pool_state_data.as_ptr().add(8) as *const PoolState;
            std::ptr::read_unaligned(pool_state_ptr)
        };

        self.token_mints_and_token_programs = TokenMintsWithTokenPrograms::new(
            account_map,
            &self.pool_state.token_0_mint,
            &self.pool_state.token_1_mint,
        );

        let amm_config_data = try_get_account_data(account_map, &self.pool_state.amm_config)?;
        self.amm_config = Some(try_deserialize_unchecked_from_bytes(amm_config_data)?);

        let get_unfrozen_token_amount = |token_vault| {
            try_get_account_data(account_map, token_vault)
                .ok()
                .and_then(|account_data| {
                    spl_token_2022::extension::StateWithExtensions::<spl_token_2022::state::Account>::unpack(account_data).ok()
                })
                .and_then(|token_account| {
                    if token_account.base.is_frozen() {
                        None
                    } else {
                        Some(token_account.base.amount)
                    }
                })
        };

        self.vault_0_amount = get_unfrozen_token_amount(&self.pool_state.token_0_vault);
        self.vault_1_amount = get_unfrozen_token_amount(&self.pool_state.token_1_vault);

        Ok(())
    }

    fn quote(&self, quote_params: &QuoteParams) -> Result<Quote> {
        if !self.pool_state.get_status_by_bit(PoolStatusBitIndex::Swap)
            || (self.timestamp.load(std::sync::atomic::Ordering::Relaxed) as u64)
                < self.pool_state.open_time
        {
            return Err(anyhow!("Pool is not trading"));
        }

        let amm_config = self.amm_config.as_ref().context("Missing AmmConfig")?;

        let zero_for_one: bool = quote_params.input_mint == self.pool_state.token_0_mint;

        let (token_mint_0, token_mint_1) = self
            .token_mints_and_token_programs
            .as_ref()
            .context("Missing mints")?
            .mints();

        let token_mint_0_transfer_fee_config =
            token_mint_0.get_extension::<TransferFeeConfig>().ok();
        let token_mint_1_transfer_fee_config =
            token_mint_1.get_extension::<TransferFeeConfig>().ok();

        let (source_mint_transfer_fee_config, destination_mint_transfer_fee_config) =
            if zero_for_one {
                (
                    token_mint_0_transfer_fee_config,
                    token_mint_1_transfer_fee_config,
                )
            } else {
                (
                    token_mint_1_transfer_fee_config,
                    token_mint_0_transfer_fee_config,
                )
            };

        let amount = quote_params.amount;
        let epoch = self.epoch.load(std::sync::atomic::Ordering::Relaxed);

        let actual_amount_in = if let Some(transfer_fee_config) = source_mint_transfer_fee_config {
            amount.saturating_sub(
                transfer_fee_config
                    .calculate_epoch_fee(epoch, amount)
                    .context("Fee calculation failure")?,
            )
        } else {
            amount
        };
        if actual_amount_in == 0 {
            return Err(anyhow!("Amount too low"));
        }

        // Calculate the trade amounts
        let (total_token_0_amount, total_token_1_amount) = match vault_amount_without_fee(
            &self.pool_state,
            self.vault_0_amount.context("Vault 0 missing or frozen")?,
            self.vault_1_amount.context("Vault 1 missing or frozen")?,
        ) {
            (Some(vault_0), Some(vault_1)) => (vault_0, vault_1),
            _ => return Err(anyhow!("Vault amount underflow")),
        };
        let (input_token_creator_rate, input_token_lp_rate) = if zero_for_one {
            (amm_config.token_0_creator_rate, amm_config.token_0_lp_rate)
        } else {
            (amm_config.token_1_creator_rate, amm_config.token_1_lp_rate)
        };

        let swap_result = raydium_cp_swap::curve::CurveCalculator::swap_base_input(
            actual_amount_in.into(),
            total_token_0_amount.into(),
            total_token_1_amount.into(),
            input_token_creator_rate,
            input_token_lp_rate
        )
        .context("Swap failed")?;
        let amount_out: u64 = swap_result.destination_amount_swapped.try_into()?;
        let actual_amount_out = if let Some(transfer_fee_config) = destination_mint_transfer_fee_config {
            amount_out.saturating_sub(
                transfer_fee_config
                    .calculate_epoch_fee(epoch, amount_out)
                    .context("Fee calculation failure")?,
            )
        } else {
            amount_out
        };

        let protocol_fee = (amm_config.token_0_creator_rate 
            + amm_config.token_1_creator_rate
            + amm_config.token_0_lp_rate 
            + amm_config.token_1_lp_rate) / 10000;

        Ok(Quote {
            in_amount: swap_result.source_amount_swapped.try_into()?,
            out_amount: actual_amount_out,
            fee_mint: quote_params.input_mint,
            fee_amount: ((amm_config.token_0_creator_rate 
                + amm_config.token_1_creator_rate
                + amm_config.token_0_lp_rate 
                + amm_config.token_1_lp_rate) + protocol_fee),
            fee_pct: rust_decimal::Decimal::from(
                (amm_config.token_0_creator_rate 
                + amm_config.token_1_creator_rate
                + amm_config.token_0_lp_rate 
                + amm_config.token_1_lp_rate) + protocol_fee
            ) / rust_decimal::Decimal::from(100),            
            ..Default::default()

        })
    }

    fn get_accounts_len(&self) -> usize {
        14
    }

    fn get_swap_and_account_metas(&self, swap_params: &SwapParams) -> Result<SwapAndAccountMetas> {
        let (token_0_token_program, token_1_token_program) = self
            .token_mints_and_token_programs
            .as_ref()
            .context("Missing programs")?
            .programs();

        let (
            input_token_program,
            input_vault,
            input_token_mint,
            output_token_program,
            output_vault,
            output_token_mint,
        ) = if swap_params.source_mint == self.pool_state.token_0_mint {
            (
                *token_0_token_program,
                self.pool_state.token_0_vault,
                self.pool_state.token_0_mint,
                *token_1_token_program,
                self.pool_state.token_1_vault,
                self.pool_state.token_1_mint,
            )
        } else {
            (
                *token_1_token_program,
                self.pool_state.token_1_vault,
                self.pool_state.token_1_mint,
                *token_0_token_program,
                self.pool_state.token_0_vault,
                self.pool_state.token_0_mint,
            )
        };

        let account_metas = SwapAccs::new(&RaydiumCpSwap {
            swap_program: Pubkey::from_str("CVF4q3yFpyQwV8DLDiJ9Ew6FFLE1vr5ToRzsXYQTaNrj").unwrap(),
            payer: swap_params.token_transfer_authority,
            authority: self.get_authority(),
            amm_config: self.pool_state.amm_config,
            pool_state: self.key,
            input_token_account: swap_params.source_token_account,
            output_token_account: swap_params.destination_token_account,
            input_vault,
            output_vault,
            input_token_program,
            output_token_program,
            input_token_mint,
            output_token_mint,
            observation_state: self.pool_state.observation_key,
        })
        .to_account_metas(None);

        Ok(SwapAndAccountMetas {
            swap: Swap::Raydium,
            account_metas,
        })
    }

    fn clone_amm(&self) -> Box<dyn Amm + Send + Sync> {
        Box::new(self.clone())
    }
}

// We are extracting this here to avoid the need to fix the contract it self.
// https://github.com/raydium-io/raydium-cp-swap/blob/master/programs/cp-swap/src/states/pool.rs#L139-L148
fn vault_amount_without_fee(
    pool: &PoolState,
    vault_0: u64,
    vault_1: u64,
) -> (Option<u64>, Option<u64>) {
    (
        vault_0.checked_sub(pool.protocol_fees_token_0 + pool.fund_fees_token_0),
        vault_1.checked_sub(pool.protocol_fees_token_1 + pool.fund_fees_token_1),
    )
}
