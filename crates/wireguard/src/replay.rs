//! The sliding window that rejects replayed transport messages (RFC 6479, as
//! in the Linux implementation; whitepaper section 5.4.6).
//!
//! The window remembers which of the last 8128 counters below the largest one
//! seen were received. A counter is accepted exactly when it is below
//! [`REJECT_AFTER_MESSAGES`], not more than [`WINDOW`] behind the largest
//! accepted, and not accepted before. This is proved in
//! `proofs/Wireguard/ReplayTop.lean` against a window described as a set of
//! seen counters.
//!
//! The bitmap is a ring of 128 words of 64 bits. Bit `v mod 8192` stands for
//! the counter `v - 1` (offset by one so that counter 0 differs from "nothing
//! seen"); when the largest counter moves forward, the words it passes are
//! cleared.

/// Counters at or above this are never accepted: `2^64 - 2^13 - 1`.
pub const REJECT_AFTER_MESSAGES: u64 = 18_446_744_073_709_543_423;
/// How far behind the largest accepted counter a counter may be: 8192 bits,
/// less one word that is reused as the window moves.
pub const WINDOW: u64 = 8128;
/// Number of words of the bitmap.
pub const WORDS: usize = 128;

/// The replay window of one receiving key.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Replay {
    /// One more than the largest accepted counter; 0 if none.
    pub top: u64,
    pub bitmap: [u64; WORDS],
}

impl Replay {
    /// A window that has seen nothing.
    pub fn new() -> Replay {
        Replay {
            top: 0,
            bitmap: [0; WORDS],
        }
    }

    /// Whether `counter` is new and recent enough; if so, it is recorded.
    pub fn check_and_update(&mut self, counter: u64) -> bool {
        if counter >= REJECT_AFTER_MESSAGES {
            return false;
        }
        let v = counter + 1;
        if v + WINDOW < self.top {
            return false;
        }
        if v > self.top {
            // Clear the words between the current top's and `v`'s (all of
            // them, at most).
            let current = self.top / 64;
            let index = v / 64;
            let n = if index - current > WORDS as u64 {
                WORDS as u64
            } else {
                index - current
            };
            let mut i = 1;
            while i <= n {
                self.bitmap[((current + i) % 128) as usize] = 0;
                i += 1;
            }
            self.top = v;
        }
        let w = ((v / 64) % 128) as usize;
        let bit = 1u64 << (v % 64);
        if self.bitmap[w] & bit != 0 {
            return false;
        }
        self.bitmap[w] |= bit;
        true
    }
}

impl Default for Replay {
    fn default() -> Self {
        Replay::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A reference window: the set of accepted counters, as a sorted list.
    struct Reference {
        seen: [u64; 4096],
        n: usize,
        max: Option<u64>,
    }

    impl Reference {
        fn accept(&mut self, c: u64) -> bool {
            if c >= REJECT_AFTER_MESSAGES {
                return false;
            }
            if let Some(m) = self.max {
                if c + 1 + WINDOW < m + 1 || self.seen[..self.n].contains(&c) {
                    return false;
                }
            }
            self.seen[self.n] = c;
            self.n += 1;
            self.max = Some(self.max.map_or(c, |m| m.max(c)));
            true
        }
    }

    /// A deterministic pseudo-random sequence.
    fn lcg(state: &mut u64) -> u64 {
        *state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        *state >> 33
    }

    #[test]
    fn matches_the_reference() {
        let mut seed = 42;
        for round in 0..20 {
            let mut w = Replay::new();
            let mut r = Reference {
                seen: [0; 4096],
                n: 0,
                max: None,
            };
            let mut base = 0u64;
            for _ in 0..2000 {
                // Mostly counters near the front, sometimes far ahead or far
                // behind, and repeats.
                let x = lcg(&mut seed);
                let c = match x % 10 {
                    0 => base + 20_000,
                    1 => base.saturating_sub(9000),
                    _ => (base + x % 300).saturating_sub(150),
                };
                base = base.max(c);
                assert_eq!(
                    w.check_and_update(c),
                    r.accept(c),
                    "round {round}, counter {c}"
                );
                if r.n == r.seen.len() {
                    break;
                }
            }
        }
    }

    #[test]
    fn window_edges() {
        let mut w = Replay::new();
        assert!(w.check_and_update(0));
        assert!(!w.check_and_update(0));
        assert!(w.check_and_update(10_000));
        // 10_000 - 8128 is the oldest acceptable.
        assert!(!w.check_and_update(10_000 - WINDOW - 1));
        assert!(w.check_and_update(10_000 - WINDOW));
        assert!(!w.check_and_update(10_000 - WINDOW));
        assert!(w.check_and_update(9_999));
        assert!(!w.check_and_update(REJECT_AFTER_MESSAGES));
        assert!(w.check_and_update(REJECT_AFTER_MESSAGES - 1));
        assert!(!w.check_and_update(REJECT_AFTER_MESSAGES - 1));
    }
}
