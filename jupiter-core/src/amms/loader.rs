use std::collections::HashSet;

use anyhow::{anyhow, Result};
use jupiter_amm_interface::{Amm, AmmContext, KeyedAccount};
use solana_sdk::pubkey::Pubkey;

use super::spl_token_swap_amm::{SplTokenSwapAmm};

pub fn amm_factory(
    keyed_account: &KeyedAccount,
    amm_context: &AmmContext,
    _saber_wrapper_mints: &mut HashSet<Pubkey>,
) -> Result<Box<dyn Amm + Send + Sync>> {
    let owner = keyed_account.account.owner;

    // Add your AMM herROGRAMS.contains_key(&owner) {
        Ok(Box::new(crate::amms::spl_token_swap_amm::Fomo3dCpAmm::from_keyed_account(
            keyed_account,
            amm_context,
        )?))
   
}