//! Arbitrary-precision natural numbers for literals (little-endian u32 limbs).

use std::cmp::Ordering;
use std::fmt;

#[derive(Clone, PartialEq, Eq, Hash, Default)]
pub struct Nat {
    limbs: Vec<u32>, // no trailing zeros; zero is the empty vector
}

impl Nat {
    pub fn zero() -> Nat {
        Nat { limbs: Vec::new() }
    }

    pub fn from_u64(v: u64) -> Nat {
        let mut n = Nat { limbs: vec![v as u32, (v >> 32) as u32] };
        n.trim();
        n
    }

    pub fn to_u64(&self) -> Option<u64> {
        match self.limbs.len() {
            0 => Some(0),
            1 => Some(self.limbs[0] as u64),
            2 => Some(self.limbs[0] as u64 | (self.limbs[1] as u64) << 32),
            _ => None,
        }
    }

    pub fn from_u128(v: u128) -> Nat {
        let mut n = Nat { limbs: vec![v as u32, (v >> 32) as u32, (v >> 64) as u32, (v >> 96) as u32] };
        n.trim();
        n
    }

    pub fn to_u128(&self) -> Option<u128> {
        if self.limbs.len() > 4 {
            return None;
        }
        Some(self.limbs.iter().enumerate().fold(0u128, |a, (i, &l)| a | (l as u128) << (32 * i)))
    }

    pub fn is_zero(&self) -> bool {
        self.limbs.is_empty()
    }

    fn trim(&mut self) {
        while self.limbs.last() == Some(&0) {
            self.limbs.pop();
        }
    }

    pub fn pow2(k: u64) -> Nat {
        let mut limbs = vec![0u32; (k / 32) as usize];
        limbs.push(1 << (k % 32));
        Nat { limbs }
    }

    pub fn add(&self, o: &Nat) -> Nat {
        let n = self.limbs.len().max(o.limbs.len());
        let mut r = Vec::with_capacity(n + 1);
        let mut carry = 0u64;
        for i in 0..n {
            let s = *self.limbs.get(i).unwrap_or(&0) as u64 + *o.limbs.get(i).unwrap_or(&0) as u64 + carry;
            r.push(s as u32);
            carry = s >> 32;
        }
        if carry > 0 {
            r.push(carry as u32);
        }
        let mut res = Nat { limbs: r };
        res.trim();
        res
    }

    /// `self - o`, or `None` if negative.
    pub fn sub(&self, o: &Nat) -> Option<Nat> {
        if self < o {
            return None;
        }
        let mut r = Vec::with_capacity(self.limbs.len());
        let mut borrow = 0i64;
        for i in 0..self.limbs.len() {
            let mut d = self.limbs[i] as i64 - *o.limbs.get(i).unwrap_or(&0) as i64 - borrow;
            borrow = 0;
            if d < 0 {
                d += 1 << 32;
                borrow = 1;
            }
            r.push(d as u32);
        }
        let mut res = Nat { limbs: r };
        res.trim();
        Some(res)
    }

    pub fn mul(&self, o: &Nat) -> Nat {
        if self.is_zero() || o.is_zero() {
            return Nat::zero();
        }
        let mut r = vec![0u64; self.limbs.len() + o.limbs.len() + 1];
        for (i, &a) in self.limbs.iter().enumerate() {
            let mut carry = 0u64;
            for (j, &b) in o.limbs.iter().enumerate() {
                let t = r[i + j] + a as u64 * b as u64 + carry;
                r[i + j] = t & 0xffff_ffff;
                carry = t >> 32;
            }
            let mut k = i + o.limbs.len();
            while carry > 0 {
                let t = r[k] + carry;
                r[k] = t & 0xffff_ffff;
                carry = t >> 32;
                k += 1;
            }
        }
        let mut res = Nat { limbs: r.into_iter().map(|x| x as u32).collect() };
        res.trim();
        res
    }

    fn bit_len(&self) -> u64 {
        match self.limbs.last() {
            None => 0,
            Some(&top) => (self.limbs.len() as u64 - 1) * 32 + (32 - top.leading_zeros() as u64),
        }
    }

    fn bit(&self, i: u64) -> bool {
        let l = (i / 32) as usize;
        l < self.limbs.len() && (self.limbs[l] >> (i % 32)) & 1 == 1
    }

    fn shl1_or(&self, bit: bool) -> Nat {
        let mut r = Vec::with_capacity(self.limbs.len() + 1);
        let mut carry = bit as u32;
        for &l in &self.limbs {
            r.push(l << 1 | carry);
            carry = l >> 31;
        }
        if carry > 0 {
            r.push(carry);
        }
        let mut res = Nat { limbs: r };
        res.trim();
        res
    }

    /// Quotient and remainder; `None` for division by zero.
    pub fn divmod(&self, d: &Nat) -> Option<(Nat, Nat)> {
        if d.is_zero() {
            return None;
        }
        if let (Some(a), Some(b)) = (self.to_u64(), d.to_u64()) {
            return Some((Nat::from_u64(a / b), Nat::from_u64(a % b)));
        }
        // binary long division: simple and obviously correct
        let mut q = Nat::zero();
        let mut r = Nat::zero();
        for i in (0..self.bit_len()).rev() {
            r = r.shl1_or(self.bit(i));
            let (nr, qb) = match r.sub(d) {
                Some(x) => (x, true),
                None => (r.clone(), false),
            };
            r = nr;
            q = q.shl1_or(qb);
        }
        Some((q, r))
    }

    pub fn parse(s: &str) -> Option<Nat> {
        let s = s.replace('_', "");
        let (digits, base) = if let Some(h) = s.strip_prefix("0x") {
            (h.to_string(), 16u64)
        } else if let Some(b) = s.strip_prefix("0b") {
            (b.to_string(), 2)
        } else {
            (s, 10)
        };
        if digits.is_empty() {
            return None;
        }
        let b = Nat::from_u64(base);
        let mut n = Nat::zero();
        for c in digits.chars() {
            let v = c.to_digit(base as u32)? as u64;
            n = n.mul(&b).add(&Nat::from_u64(v));
        }
        Some(n)
    }

    pub fn to_hex(&self) -> String {
        if self.is_zero() {
            return "0x0".into();
        }
        let mut s = format!("0x{:x}", self.limbs.last().unwrap());
        for l in self.limbs.iter().rev().skip(1) {
            s.push_str(&format!("{:08x}", l));
        }
        s
    }
}

impl Ord for Nat {
    fn cmp(&self, o: &Nat) -> Ordering {
        self.limbs
            .len()
            .cmp(&o.limbs.len())
            .then_with(|| self.limbs.iter().rev().cmp(o.limbs.iter().rev()))
    }
}

impl PartialOrd for Nat {
    fn partial_cmp(&self, o: &Nat) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}

impl fmt::Display for Nat {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(v) = self.to_u64() {
            return write!(f, "{}", v);
        }
        // large numbers are printed in hex (exact, and cheap)
        write!(f, "{}", self.to_hex())
    }
}

impl fmt::Debug for Nat {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn arithmetic() {
        let a = Nat::parse("0xffffffffffffffffffff").unwrap();
        let b = Nat::from_u64(12345);
        let (q, r) = a.divmod(&b).unwrap();
        assert_eq!(q.mul(&b).add(&r), a);
        assert!(r < b);
        assert_eq!(Nat::pow2(64).sub(&Nat::from_u64(1)).unwrap().to_u64(), Some(u64::MAX));
        assert_eq!(Nat::parse("1_000").unwrap().to_u64(), Some(1000));
        assert_eq!(Nat::parse("0b101").unwrap().to_u64(), Some(5));
        assert_eq!(Nat::from_u64(3).sub(&Nat::from_u64(4)), None);
    }
}
