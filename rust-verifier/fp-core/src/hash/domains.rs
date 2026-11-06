//! Domain-separation numbers, ported from `blocks/hash/domains.h`.
//!
//! Each use of `H(tag, index, start; bytes)` has its own number: the tag's low 16 bits.

/// The domain-separation numbers of this format.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum Domain {
    ChainStart = 160,
    ChainQuery = 162,
    LeafMain = 164,
    TreeNode = 166,
    Statement = 168,
    Parameters = 169,
    TestCoins = 171,
    Run = 172,
    LeafBinding = 173,
    LeafStoredMain = 174,
    CoinInputs = 176,
    Reserved = 177,
    BindingNode = 178,
    PublishedId = 179,
}

impl Domain {
    #[inline]
    pub const fn from_word(w: u32) -> Self {
        match w {
            160 => Domain::ChainStart,
            162 => Domain::ChainQuery,
            164 => Domain::LeafMain,
            166 => Domain::TreeNode,
            168 => Domain::Statement,
            169 => Domain::Parameters,
            171 => Domain::TestCoins,
            172 => Domain::Run,
            173 => Domain::LeafBinding,
            174 => Domain::LeafStoredMain,
            176 => Domain::CoinInputs,
            177 => Domain::Reserved,
            178 => Domain::BindingNode,
            179 => Domain::PublishedId,
            _ => panic!("not a domain number of this format"),
        }
    }
}

/// True for every number but `Reserved` (`domain_is_given_out`).
#[inline]
pub const fn domain_is_given_out(d: Domain) -> bool {
    !matches!(d, Domain::Reserved)
}

/// True if the start is stored in the tag (`domain_start_in_tag`).
#[inline]
pub const fn domain_start_in_tag(d: Domain) -> bool {
    matches!(
        d,
        Domain::LeafMain
            | Domain::TreeNode
            | Domain::LeafBinding
            | Domain::LeafStoredMain
            | Domain::BindingNode
    )
}

#[inline]
pub const fn domain_is_leaf(d: Domain) -> bool {
    matches!(
        d,
        Domain::LeafMain | Domain::LeafBinding | Domain::LeafStoredMain
    )
}

#[inline]
pub const fn domain_is_vertex(d: Domain) -> bool {
    matches!(d, Domain::TreeNode | Domain::BindingNode)
}

/// `domain_has_start`: a start comes with each hash, or is in the tag.
#[inline]
pub const fn domain_has_start(d: Domain) -> bool {
    domain_start_in_tag(d) || matches!(d, Domain::ChainQuery | Domain::TestCoins)
}
