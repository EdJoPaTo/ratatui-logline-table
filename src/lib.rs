#![allow(clippy::cast_possible_truncation)]
#![cfg_attr(not(test), no_std)]
extern crate alloc;

pub use highlight_spacing::HighlightSpacing;
pub use state::State;
pub use table::Table;

mod highlight_spacing;
mod state;
mod table;
