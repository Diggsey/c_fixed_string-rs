//! The goal of this crate is to provide a safe wrapper around the notion of
//! a C-style string with a predefined maximum length, known as the *limit*.
//! 
//! CFixedString and CFixedStr are the owning and non-owning variants
//! respectively.
extern crate memchr;

use std::os::raw::c_char;
use std::{slice, str, fmt, ascii, ops, ptr, mem};
use std::borrow::{Cow,Borrow};
use std::hash::{Hash, Hasher};
use std::ffi::{CStr, CString};
use std::cmp::Ordering;
use std::error::Error;

use memchr::memchr;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct IntoStringError {
    inner: CFixedString,
    error: str::Utf8Error,
}

impl IntoStringError {
    /// Consumes this error, returning original [`CFixedString`] which generated the
    /// error.
    ///
    /// [`CFixedString`]: struct.CFixedString.html
    pub fn into_c_fixed_string(self) -> CFixedString {
        self.inner
    }

    /// Access the underlying UTF-8 error that was the cause of this error.
    pub fn utf8_error(&self) -> str::Utf8Error {
        self.error
    }
}

impl Error for IntoStringError {
    fn description(&self) -> &str {
        "C fixed string contained non-utf8 bytes"
    }

    fn cause(&self) -> Option<&Error> {
        Some(&self.error)
    }
}

impl fmt::Display for IntoStringError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.description().fmt(f)
    }
}

/// This type owns a fixed length buffer containing a C-style string.
/// The string is terminated by the first null byte in the buffer, or by the
/// length of the buffer if no null byte is present.
///
/// The length of the buffer is known as the *limit* of the CFixedString.
/// The `len()` method returns the length of the string within the buffer.
///
/// Any bytes after the first null byte are not considered part of the string
/// and may contain garbage data. When comparing or hashing CFixedStrings,
/// these bytes are not included.
///
/// # Performance
///
/// Be aware that many of the methods on this type which would normally be
/// expected to run in constant time may run in time linear in the length of
/// the string. For this reason, it is recommended to use the type only for
/// interop with C code, and to convert to a standard string or byte buffer
/// as soon as possible.
pub struct CFixedString {
    inner: Box<[u8]>
}

impl CFixedString {
    /// Construct a new fixed-length C string from a byte slice
    /// The first null byte terminates the string, but the length
    /// of the slice determines the limit of this fixed-size string.
    pub fn new<T: Into<Box<[u8]>>>(t: T) -> CFixedString {
        CFixedString { inner: t.into() }
    }
    /// Construct an empty string with the specified limit. The buffer
    /// is entirely zero-initialized.
    pub fn with_limit(limit: usize) -> CFixedString {
        CFixedString { inner: vec![0; limit].into_boxed_slice() }
    }
    /// Retakes ownership of a CFixedString that was transferred to C.
    ///
    /// # Safety
    ///
    /// This should only ever be called with a pointer and limit that was earlier
    /// obtained from a CFixedString. The previous string must have been forgotten
    /// to ensure that the memory has not already been freed.
    pub unsafe fn from_raw_parts(ptr: *mut c_char, limit: usize) -> CFixedString {
        CFixedString {
            inner: Box::from_raw(slice::from_raw_parts_mut(ptr as *mut u8, limit))
        }
    }
    /// Converts the CFixedString into a String if it contains valid Unicode data.
    ///
    /// On failure, ownership of the original CFixedString is returned.
    pub fn into_string(self) -> Result<String, IntoStringError> {
        String::from_utf8(self.into_bytes())
            .map_err(|e| IntoStringError {
                error: e.utf8_error(),
                inner: CFixedString::new(e.into_bytes()),
            })
    }
    /// Converts the CFixedString into a CString. If necessary, the buffer will be
    /// extended to make room for a final null byte. If the buffer does not need
    /// to be extended, no allocation will be performed.
    pub fn into_c_string(self) -> CString {
        unsafe { CString::from_vec_unchecked(self.into_bytes()) }
    }
    /// Converts the CFixedString into a byte buffer. The length of the buffer will
    /// equal the length of the string up to but not including the first null byte.
    /// The capacity of the buffer will equal the limit of the CFixedString.
    pub fn into_bytes(self) -> Vec<u8> {
        let l = self.len();
        let mut v = self.into_inner().into_vec();
        v.truncate(l);
        v
    }
    /// Converts the CFixedString into a byte buffer. The length of the buffer will
    /// equal the limit of the CFixedString. The buffer may contain garbage
    /// values after the first null byte.
    pub fn into_bytes_full(self) -> Vec<u8> {
        self.into_inner().into_vec()
    }
    /// Extracts a CFixedStr slice containing the entire buffer.
    pub fn as_c_fixed_str(&self) -> &CFixedStr {
        &*self
    }
    /// Extracts a mutable CFixedStr slice containing the entire buffer.
    pub fn as_c_fixed_str_mut(&mut self) -> &mut CFixedStr {
        &mut *self
    }
    /// Converts this CFixedString into a boxed CFixedStr
    pub fn into_boxed_c_fixed_str(self) -> Box<CFixedStr> {
        unsafe { Box::from_raw(Box::into_raw(self.into_inner()) as *mut CFixedStr) }
    }
    fn into_inner(self) -> Box<[u8]> {
        unsafe {
            let result = ptr::read(&self.inner);
            mem::forget(self);
            result
        }
    }
}

impl Drop for CFixedString {
    #[inline]
    fn drop(&mut self) {
        if let Some(c) = self.inner.first_mut() {
            *c = 0
        }
    }
}

impl ops::Deref for CFixedString {
    type Target = CFixedStr;

    #[inline]
    fn deref(&self) -> &CFixedStr {
        CFixedStr::from_bytes(&self.inner)
    }
}

impl ops::DerefMut for CFixedString {
    #[inline]
    fn deref_mut(&mut self) -> &mut CFixedStr {
        CFixedStr::from_bytes_mut(&mut self.inner)
    }
}

impl fmt::Debug for CFixedString {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl Clone for CFixedString {
    fn clone(&self) -> Self {
        CFixedString::new(self.as_bytes_full())
    }
}

impl Hash for CFixedString {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (**self).hash(state);
    }
}

impl PartialEq for CFixedString {
    fn eq(&self, other: &CFixedString) -> bool {
        (**self).eq(other)
    }
}

impl Eq for CFixedString {}

impl PartialOrd for CFixedString {
    fn partial_cmp(&self, other: &CFixedString) -> Option<Ordering> {
        (**self).partial_cmp(other)
    }
}

impl Ord for CFixedString {
    fn cmp(&self, other: &CFixedString) -> Ordering {
        (**self).cmp(other)
    }
}

impl From<CFixedString> for Vec<u8> {
    #[inline]
    fn from(s: CFixedString) -> Vec<u8> {
        s.into_bytes()
    }
}

/// This type represents a view of a fixed length buffer containing a C-style string.
/// The string is terminated by the first null byte in the buffer, or by the
/// length of the buffer if no null byte is present.
/// 
/// The length of the buffer is known as the *limit* of the CFixedStr.
/// The `len()` method returns the length of the string within the buffer.
/// 
/// Any bytes after the first null byte are not considered part of the string
/// and may contain garbage data. When comparing or hashing CFixedStrs,
/// these bytes are not included.
///
/// # Performance
/// 
/// Be aware that many of the methods on this type which would normally be
/// expected to run in constant time may run in time linear in the length of
/// the string. For this reason, it is recommended to use the type only for
/// interop with C code, and to convert to a standard string or byte buffer
/// as soon as possible.
pub struct CFixedStr {
    inner: [u8]
}

impl CFixedStr {
    /// Cast a raw C-style buffer to a CFixedStr.
    pub unsafe fn from_ptr<'a>(ptr: *const c_char, limit: usize) -> &'a CFixedStr {
        Self::from_bytes(slice::from_raw_parts(ptr as *const u8, limit))
    }
    /// Cast a raw C-style buffer to a mutable CFixedStr.
    pub unsafe fn from_mut_ptr<'a>(ptr: *mut c_char, limit: usize) -> &'a mut CFixedStr {
        Self::from_bytes_mut(slice::from_raw_parts_mut(ptr as *mut u8, limit))
    }
    /// Create a CFixedStr from a string slice.
    pub fn from_str(s: &str) -> &CFixedStr {
        Self::from_bytes(s.as_bytes())
    }
    /// Create a CFixedStr from a byte slice.
    pub fn from_bytes(bytes: &[u8]) -> &CFixedStr {
        unsafe { &*(bytes as *const [u8] as *const CFixedStr) }
    }
    /// Create a CFixedStr from a mutable byte slice.
    pub fn from_bytes_mut(bytes: &mut [u8]) -> &mut CFixedStr {
        unsafe { &mut *(bytes as *mut [u8] as *mut CFixedStr) }
    }
    /// Create a CFixedStr from a variable length CStr.
    pub fn from_c_str(c_str: &CStr) -> &CFixedStr {
        Self::from_bytes(c_str.to_bytes_with_nul())
    }
    /// Returns the inner pointer to this CFixedStr.
    ///
    /// # Safety
    /// 
    /// It is your responsibility to make sure the underlying memory is not
    /// freed to early.
    pub fn as_ptr(&self) -> *const c_char {
        self.inner.as_ptr() as *const c_char
    }
    /// Returns the inner pointer to this mutable CFixedStr.
    ///
    /// # Safety
    /// 
    /// It is your responsibility to make sure the underlying memory is not
    /// freed to early.
    pub fn as_mut_ptr(&mut self) -> *mut c_char {
        self.inner.as_mut_ptr() as *mut c_char
    }
    /// Returns the limit of this CFixedStr. This corresponds to the longest
    /// possible string that could be stored here.
    pub fn limit(&self) -> usize {
        self.inner.len()
    }
    /// Returns the length of the CFixedStr. This operation takes linear time.
    pub fn len(&self) -> usize {
        memchr(0, &self.inner).unwrap_or(self.limit())
    }
    /// Coverts this CFixedStr to a byte slice. The length of the slice is equal
    /// to the length of the string up to but not including the first null byte.
    pub fn to_bytes(&self) -> &[u8] {
        &self.inner[0..self.len()]
    }
    /// Coverts this CFixedStr to a mutable byte slice. The length of the slice is equal
    /// to the length of the string up to but not including the first null byte.
    pub fn to_bytes_mut(&mut self) -> &mut [u8] {
        let l = self.len();
        &mut self.inner[0..l]
    }
    /// Coverts this CFixedStr to a byte slice. The length of the slice is equal
    /// to the length of the string up to and including the first null byte, if it exists.
    pub fn to_bytes_extended(&self) -> &[u8] {
        if let Some(l) = memchr(0, &self.inner) {
            &self.inner[0 .. l+1]
        } else {
            &self.inner
        }
    }
    /// Coverts this CFixedStr to a mutable byte slice. The length of the slice is equal
    /// to the length of the string up to and including the first null byte, if it exists.
    pub fn to_bytes_mut_extended(&mut self) -> &mut [u8] {
        if let Some(l) = memchr(0, &self.inner) {
            &mut self.inner[0 .. l+1]
        } else {
            &mut self.inner
        }
    }
    /// Coverts this CFixedStr to a byte slice. The length of the slice is equal
    /// to the limit of the CFixedStr.
    pub fn as_bytes_full(&self) -> &[u8] {
        &self.inner
    }
    /// Coverts this CFixedStr to a mutable byte slice. The length of the slice is equal
    /// to the limit of the CFixedStr.
    pub fn as_bytes_mut_full(&mut self) -> &mut [u8] {
        &mut self.inner
    }
    /// Yields a &str slice if the CFixedStr contains valid UTF-8.
    ///
    /// This function will calculate the length of this string and check for UTF-8 validity,
    /// and then return the &str if it's valid.
    pub fn to_str(&self) -> Result<&str, str::Utf8Error> {
        str::from_utf8(self.to_bytes())
    }
    /// Converts a CFixedStr into a Cow<str>.
    ///
    /// This function will calculate the length of this string and then return the resulting
    /// slice as a `Cow<str>`, replacing any invalid UTF-8 sequences with `U+FFFD REPLACEMENT CHARACTER`.
    pub fn to_string_lossy(&self) -> Cow<str> {
        String::from_utf8_lossy(self.to_bytes())
    }
    /// Converts a CFixedStr into a Cow<CStr>.
    ///
    /// This function will calculate the length of this string, and then ensure it has a
    /// terminating null byte. If a null byte is already present, the `Borrowed` variant
    /// can be returned.
    pub fn to_c_str(&self) -> Cow<CStr> {
        if let Some(l) = memchr(0, &self.inner) {
            Cow::Borrowed(unsafe { CStr::from_bytes_with_nul_unchecked(&self.inner[0 .. l+1]) })
        } else {
            let mut v = Vec::with_capacity(self.inner.len() + 1);
            v.extend(&self.inner);
            Cow::Owned(unsafe { CString::from_vec_unchecked(v) })
        }
    }
    /// Converts a `Box<CFixedStr>` into a `CFixedString` without copying or allocating.
    pub fn into_c_fixed_string(self: Box<CFixedStr>) -> CFixedString {
        let raw = Box::into_raw(self) as *mut [u8];
        CFixedString { inner: unsafe { Box::from_raw(raw) } }
    }
}

impl Hash for CFixedStr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.to_bytes().hash(state);
    }
}

impl fmt::Debug for CFixedStr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "\"")?;
        for byte in self.to_bytes().iter().flat_map(|&b| ascii::escape_default(b)) {
            fmt::Write::write_char(f, byte as char)?;
        }
        write!(f, "\"")
    }
}

impl<'a> Default for &'a CFixedStr {
    fn default() -> &'a CFixedStr {
        const SLICE: &'static [u8] = &[0];
        CFixedStr::from_bytes(SLICE)
    }
}

impl Default for CFixedString {
    fn default() -> CFixedString {
        CFixedString { inner: Default::default() }
    }
}

impl Borrow<CFixedStr> for CFixedString {
    #[inline]
    fn borrow(&self) -> &CFixedStr { self }
}

impl PartialEq for CFixedStr {
    fn eq(&self, other: &CFixedStr) -> bool {
        self.to_bytes().eq(other.to_bytes())
    }
}

impl Eq for CFixedStr {}

impl PartialOrd for CFixedStr {
    fn partial_cmp(&self, other: &CFixedStr) -> Option<Ordering> {
        self.to_bytes().partial_cmp(&other.to_bytes())
    }
}

impl Ord for CFixedStr {
    fn cmp(&self, other: &CFixedStr) -> Ordering {
        self.to_bytes().cmp(&other.to_bytes())
    }
}

impl ToOwned for CFixedStr {
    type Owned = CFixedString;

    fn to_owned(&self) -> CFixedString {
        CFixedString { inner: self.to_bytes_extended().into() }
    }
}

impl<'a> From<&'a CFixedStr> for CFixedString {
    fn from(s: &'a CFixedStr) -> CFixedString {
        s.to_owned()
    }
}

impl ops::Index<ops::RangeFull> for CFixedString {
    type Output = CFixedStr;

    #[inline]
    fn index(&self, _index: ops::RangeFull) -> &CFixedStr {
        self
    }
}

impl ops::IndexMut<ops::RangeFull> for CFixedString {
    #[inline]
    fn index_mut(&mut self, _index: ops::RangeFull) -> &mut CFixedStr {
        self
    }
}

impl AsRef<CFixedStr> for CFixedStr {
    #[inline]
    fn as_ref(&self) -> &CFixedStr {
        self
    }
}

impl AsRef<CFixedStr> for CFixedString {
    #[inline]
    fn as_ref(&self) -> &CFixedStr {
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn it_works() {
        assert_eq!(&CFixedString::new(&b"hello,\0world!\0"[..])[..], CFixedStr::from_str("hello,"));
    }
}
