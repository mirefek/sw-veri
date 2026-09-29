//! Arbitrary-precision signed integers for the interpreter.

use std::cmp::Ordering;
use std::fmt;

/// sign + magnitude; magnitude little-endian u64 limbs, no trailing zeros
#[derive(Clone, PartialEq, Eq, Hash, Default)]
pub struct Int {
    neg: bool,
    mag: Vec<u64>,
}

fn trim(v: &mut Vec<u64>) {
    while v.last() == Some(&0) {
        v.pop();
    }
}

fn cmp_mag(a: &[u64], b: &[u64]) -> Ordering {
    a.len().cmp(&b.len()).then_with(|| a.iter().rev().cmp(b.iter().rev()))
}

fn add_mag(a: &[u64], b: &[u64]) -> Vec<u64> {
    let mut r = Vec::with_capacity(a.len().max(b.len()) + 1);
    let mut carry = 0u128;
    for i in 0..a.len().max(b.len()) {
        let s = *a.get(i).unwrap_or(&0) as u128 + *b.get(i).unwrap_or(&0) as u128 + carry;
        r.push(s as u64);
        carry = s >> 64;
    }
    if carry > 0 {
        r.push(carry as u64);
    }
    r
}

/// a - b for |a| >= |b|
fn sub_mag(a: &[u64], b: &[u64]) -> Vec<u64> {
    let mut r = Vec::with_capacity(a.len());
    let mut borrow = 0i128;
    for i in 0..a.len() {
        let mut d = a[i] as i128 - *b.get(i).unwrap_or(&0) as i128 - borrow;
        borrow = 0;
        if d < 0 {
            d += 1 << 64;
            borrow = 1;
        }
        r.push(d as u64);
    }
    trim(&mut r);
    r
}

fn mul_mag(a: &[u64], b: &[u64]) -> Vec<u64> {
    let mut r = vec![0u64; a.len() + b.len() + 1];
    for (i, &x) in a.iter().enumerate() {
        let mut carry = 0u128;
        for (j, &y) in b.iter().enumerate() {
            let t = r[i + j] as u128 + x as u128 * y as u128 + carry;
            r[i + j] = t as u64;
            carry = t >> 64;
        }
        let mut k = i + b.len();
        while carry > 0 {
            let t = r[k] as u128 + carry;
            r[k] = t as u64;
            carry = t >> 64;
            k += 1;
        }
    }
    trim(&mut r);
    r
}

fn bits_of(a: &[u64]) -> u64 {
    match a.last() {
        None => 0,
        Some(&t) => (a.len() as u64 - 1) * 64 + 64 - t.leading_zeros() as u64,
    }
}

fn bit(a: &[u64], i: u64) -> bool {
    let l = (i / 64) as usize;
    l < a.len() && (a[l] >> (i % 64)) & 1 == 1
}

fn shl_mag(a: &[u64], k: u64) -> Vec<u64> {
    if a.is_empty() {
        return vec![];
    }
    let (w, b) = ((k / 64) as usize, k % 64);
    let mut r = vec![0u64; w];
    let mut carry = 0u64;
    for &x in a {
        r.push(if b == 0 { x } else { x << b | carry });
        carry = if b == 0 { 0 } else { x >> (64 - b) };
    }
    if carry > 0 {
        r.push(carry);
    }
    trim(&mut r);
    r
}

fn shr_mag(a: &[u64], k: u64) -> Vec<u64> {
    let (w, b) = ((k / 64) as usize, k % 64);
    if w >= a.len() {
        return vec![];
    }
    let mut r = Vec::with_capacity(a.len() - w);
    for i in w..a.len() {
        let lo = a[i] >> b;
        let hi = if b == 0 { 0 } else { a.get(i + 1).map(|x| x << (64 - b)).unwrap_or(0) };
        r.push(lo | hi);
    }
    trim(&mut r);
    r
}

/// quotient and remainder of magnitudes (b != 0)
fn divmod_mag(a: &[u64], b: &[u64]) -> (Vec<u64>, Vec<u64>) {
    if cmp_mag(a, b) == Ordering::Less {
        return (vec![], a.to_vec());
    }
    if a.len() <= 2 && b.len() <= 2 {
        let x = a.first().copied().unwrap_or(0) as u128 | (a.get(1).copied().unwrap_or(0) as u128) << 64;
        let y = b.first().copied().unwrap_or(0) as u128 | (b.get(1).copied().unwrap_or(0) as u128) << 64;
        let (q, r) = (x / y, x % y);
        let mut qv = vec![q as u64, (q >> 64) as u64];
        let mut rv = vec![r as u64, (r >> 64) as u64];
        trim(&mut qv);
        trim(&mut rv);
        return (qv, rv);
    }
    let mut q = vec![0u64; a.len()];
    let mut r: Vec<u64> = vec![];
    for i in (0..bits_of(a)).rev() {
        r = shl_mag(&r, 1);
        if bit(a, i) {
            if r.is_empty() {
                r.push(1);
            } else {
                r[0] |= 1;
            }
        }
        if cmp_mag(&r, b) != Ordering::Less {
            r = sub_mag(&r, b);
            q[(i / 64) as usize] |= 1 << (i % 64);
        }
    }
    trim(&mut q);
    (q, r)
}

impl Int {
    pub fn zero() -> Int {
        Int::default()
    }
    pub fn from_i128(v: i128) -> Int {
        let neg = v < 0;
        let m = v.unsigned_abs();
        let mut mag = vec![m as u64, (m >> 64) as u64];
        trim(&mut mag);
        Int { neg, mag }
    }
    pub fn from_u128(v: u128) -> Int {
        let mut mag = vec![v as u64, (v >> 64) as u64];
        trim(&mut mag);
        Int { neg: false, mag }
    }
    fn mk(neg: bool, mag: Vec<u64>) -> Int {
        let neg = neg && !mag.is_empty();
        Int { neg, mag }
    }
    pub fn is_zero(&self) -> bool {
        self.mag.is_empty()
    }
    pub fn is_neg(&self) -> bool {
        self.neg
    }
    pub fn pow2(k: u64) -> Int {
        Int::mk(false, shl_mag(&[1], k))
    }
    /// value if it fits in i128
    pub fn to_i128(&self) -> Option<i128> {
        if self.mag.len() > 2 {
            return None;
        }
        let m = self.mag.first().copied().unwrap_or(0) as u128 | (self.mag.get(1).copied().unwrap_or(0) as u128) << 64;
        if m > i128::MAX as u128 {
            return None;
        }
        Some(if self.neg { -(m as i128) } else { m as i128 })
    }
    pub fn to_u64(&self) -> Option<u64> {
        if self.neg || self.mag.len() > 1 {
            return None;
        }
        Some(self.mag.first().copied().unwrap_or(0))
    }
    pub fn add(&self, o: &Int) -> Int {
        if self.neg == o.neg {
            return Int::mk(self.neg, add_mag(&self.mag, &o.mag));
        }
        match cmp_mag(&self.mag, &o.mag) {
            Ordering::Less => Int::mk(o.neg, sub_mag(&o.mag, &self.mag)),
            _ => Int::mk(self.neg, sub_mag(&self.mag, &o.mag)),
        }
    }
    pub fn neg(&self) -> Int {
        Int::mk(!self.neg, self.mag.clone())
    }
    pub fn sub(&self, o: &Int) -> Int {
        self.add(&o.neg())
    }
    pub fn mul(&self, o: &Int) -> Int {
        Int::mk(self.neg != o.neg, mul_mag(&self.mag, &o.mag))
    }
    /// Euclidean division (remainder >= 0), as in the prelude's `int_div`.
    pub fn div_euclid(&self, o: &Int) -> Option<(Int, Int)> {
        if o.is_zero() {
            return None;
        }
        let (q, r) = divmod_mag(&self.mag, &o.mag);
        let (mut q, mut r) = (Int::mk(self.neg != o.neg, q), Int::mk(self.neg, r));
        if r.neg {
            // r < 0: r += |o|, q -= sign(o)
            r = r.add(&Int::mk(false, o.mag.clone()));
            q = if o.neg { q.add(&Int::from_i128(1)) } else { q.sub(&Int::from_i128(1)) };
        }
        Some((q, r))
    }
    /// x mod 2^w (always non-negative)
    pub fn wrap(&self, w: u32) -> Int {
        let m = Int::pow2(w as u64);
        self.div_euclid(&m).unwrap().1
    }
    pub fn pow(&self, e: u64) -> Int {
        let mut r = Int::from_i128(1);
        for _ in 0..e {
            r = r.mul(self);
        }
        r
    }
    pub fn shl(&self, k: u64) -> Int {
        Int::mk(self.neg, shl_mag(&self.mag, k))
    }
    /// floor(x / 2^k) for x >= 0
    pub fn shr(&self, k: u64) -> Int {
        Int::mk(false, shr_mag(&self.mag, k))
    }
    pub fn bit(&self, i: u64) -> bool {
        bit(&self.mag, i)
    }
    /// bitwise operations on non-negative numbers
    pub fn bitop(&self, o: &Int, f: impl Fn(u64, u64) -> u64) -> Int {
        let n = self.mag.len().max(o.mag.len());
        let mut r: Vec<u64> = (0..n).map(|i| f(*self.mag.get(i).unwrap_or(&0), *o.mag.get(i).unwrap_or(&0))).collect();
        trim(&mut r);
        Int::mk(false, r)
    }
    /// bitwise not within w bits (x non-negative, below 2^w)
    pub fn not_w(&self, w: u32) -> Int {
        Int::pow2(w as u64).sub(&Int::from_i128(1)).sub(self)
    }
    pub fn to_hex(&self) -> String {
        if self.mag.is_empty() {
            return "0x0".into();
        }
        let mut s = format!("{}0x{:x}", if self.neg { "-" } else { "" }, self.mag.last().unwrap());
        for l in self.mag.iter().rev().skip(1) {
            s.push_str(&format!("{:016x}", l));
        }
        s
    }
}

impl Ord for Int {
    fn cmp(&self, o: &Int) -> Ordering {
        match (self.neg, o.neg) {
            (false, true) => Ordering::Greater,
            (true, false) => Ordering::Less,
            (false, false) => cmp_mag(&self.mag, &o.mag),
            (true, true) => cmp_mag(&o.mag, &self.mag),
        }
    }
}

impl PartialOrd for Int {
    fn partial_cmp(&self, o: &Int) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}

impl fmt::Display for Int {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.to_i128() {
            Some(v) => write!(f, "{}", v),
            None => write!(f, "{}", self.to_hex()),
        }
    }
}

impl fmt::Debug for Int {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

#[cfg(test)]
mod tests {
    use super::Int;

    #[test]
    fn arithmetic() {
        let a = Int::pow2(128).sub(&Int::from_i128(1));
        assert_eq!(a.add(&Int::from_i128(1)), Int::pow2(128));
        let (q, r) = Int::from_i128(-7).div_euclid(&Int::from_i128(2)).unwrap();
        assert_eq!((q.to_i128(), r.to_i128()), (Some(-4), Some(1)));
        assert_eq!(Int::from_i128(-1).wrap(64).to_u64(), Some(u64::MAX));
        assert_eq!(a.shr(120).to_i128(), Some(255));
        let big = Int::pow2(100).add(&Int::from_i128(12345));
        let (q, r) = big.div_euclid(&Int::from_i128(1000)).unwrap();
        assert_eq!(q.mul(&Int::from_i128(1000)).add(&r), big);
        assert_eq!(Int::from_i128(0b1100).bitop(&Int::from_i128(0b1010), |x, y| x ^ y).to_i128(), Some(0b0110));
    }
}
