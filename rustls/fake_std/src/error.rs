//! Traits for working with Errors.

// A note about crates and the facade:
//
// Originally, the `Error` trait was defined in libcore, and the impls
// were scattered about. However, coherence objected to this
// arrangement, because to create the blanket impls for `Box` required
// knowing that `&str: !Error`, and we have no means to deal with that
// sort of conflict just now. Therefore, for the time being, we have
// moved the `Error` trait into libstd. As we evolve a sol'n to the
// coherence challenge (e.g., specialization, neg impls, etc) we can
// reconsider what crate these items belong in.

#[cfg(test)]
mod tests;

use core::array;
use core::convert::Infallible;

// use alloc::{AllocError, LayoutErr};
use core::any::TypeId;
// use crate::backtrace::Backtrace;
use alloc::borrow::Cow;
use core::cell;
use core::char;
use core::fmt::{self, Debug, Display};
use core::num;
use core::str;
use alloc::string;
use alloc::string::String;
use alloc::boxed::Box;


/// `Error` is a trait representing the basic expectations for error values,
/// i.e., values of type `E` in [`Result<T, E>`]. Errors must describe
/// themselves through the [`Display`] and [`Debug`] traits, and may provide
/// cause chain information:
///
/// [`Error::source()`] is generally used when errors cross
/// "abstraction boundaries". If one module must report an error that is caused
/// by an error from a lower-level module, it can allow accessing that error
/// via [`Error::source()`]. This makes it possible for the high-level
/// module to provide its own errors while also revealing some of the
/// implementation for debugging via `source` chains.
///
/// [`Result<T, E>`]: Result
pub trait Error: Debug + Display {
    /// The lower-level source of this error, if any.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::error::Error;
    /// use std::fmt;
    ///
    /// #[derive(Debug)]
    /// struct SuperError {
    ///     side: SuperErrorSideKick,
    /// }
    ///
    /// impl fmt::Display for SuperError {
    ///     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    ///         write!(f, "SuperError is here!")
    ///     }
    /// }
    ///
    /// impl Error for SuperError {
    ///     fn source(&self) -> Option<&(dyn Error + 'static)> {
    ///         Some(&self.side)
    ///     }
    /// }
    ///
    /// #[derive(Debug)]
    /// struct SuperErrorSideKick;
    ///
    /// impl fmt::Display for SuperErrorSideKick {
    ///     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    ///         write!(f, "SuperErrorSideKick is here!")
    ///     }
    /// }
    ///
    /// impl Error for SuperErrorSideKick {}
    ///
    /// fn get_super_error() -> Result<(), SuperError> {
    ///     Err(SuperError { side: SuperErrorSideKick })
    /// }
    ///
    /// fn main() {
    ///     match get_super_error() {
    ///         Err(e) => {
    ///             println!("Error: {}", e);
    ///             println!("Caused by: {}", e.source().unwrap());
    ///         }
    ///         _ => println!("No error"),
    ///     }
    /// }
    /// ```
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }

    /// Gets the `TypeId` of `self`.
    fn type_id(&self, _: private::Internal) -> TypeId
    where
        Self: 'static,
    {
        TypeId::of::<Self>()
    }

    /// Returns a stack backtrace, if available, of where this error occurred.
    ///
    /// This function allows inspecting the location, in code, of where an error
    /// happened. The returned `Backtrace` contains information about the stack
    /// trace of the OS thread of execution of where the error originated from.
    ///
    /// Note that not all errors contain a `Backtrace`. Also note that a
    /// `Backtrace` may actually be empty. For more information consult the
    /// `Backtrace` type itself.
    //
    // fn backtrace(&self) -> Option<&Backtrace> {
    //     None
    // }

    /// ```
    /// if let Err(e) = "xc".parse::<u32>() {
    ///     // Print `e` itself, no need for description().
    ///     eprintln!("Error: {}", e);
    /// }
    /// ```
    fn description(&self) -> &str {
        "description() is deprecated; use Display"
    }
    fn cause(&self) -> Option<&dyn Error> {
        self.source()
    }
}

mod private {
    // This is a hack to prevent `type_id` from being overridden by `Error`
    // implementations, since that can enable unsound downcasting.

    #[derive(Debug)]
    pub struct Internal;
}

impl<'a, E: Error + 'a> From<E> for Box<dyn Error + 'a> {
    /// Converts a type of [`Error`] into a box of dyn [`Error`].
    ///
    /// # Examples
    ///
    /// ```
    /// use std::error::Error;
    /// use std::fmt;
    /// use std::mem;
    ///
    /// #[derive(Debug)]
    /// struct AnError;
    ///
    /// impl fmt::Display for AnError {
    ///     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    ///         write!(f , "An error")
    ///     }
    /// }
    ///
    /// impl Error for AnError {}
    ///
    /// let an_error = AnError;
    /// assert!(0 == mem::size_of_val(&an_error));
    /// let a_boxed_error = Box::<dyn Error>::from(an_error);
    /// assert!(mem::size_of::<Box<dyn Error>>() == mem::size_of_val(&a_boxed_error))
    /// ```
    fn from(err: E) -> Box<dyn Error + 'a> {
        Box::new(err)
    }
}

impl<'a, E: Error + Send + Sync + 'a> From<E> for Box<dyn Error + Send + Sync + 'a> {
    /// Converts a type of [`Error`] + [`Send`] + [`Sync`] into a box of
    /// dyn [`Error`] + [`Send`] + [`Sync`].
    ///
    /// # Examples
    ///
    /// ```
    /// use std::error::Error;
    /// use std::fmt;
    /// use std::mem;
    ///
    /// #[derive(Debug)]
    /// struct AnError;
    ///
    /// impl fmt::Display for AnError {
    ///     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    ///         write!(f , "An error")
    ///     }
    /// }
    ///
    /// impl Error for AnError {}
    ///
    /// unsafe impl Send for AnError {}
    ///
    /// unsafe impl Sync for AnError {}
    ///
    /// let an_error = AnError;
    /// assert!(0 == mem::size_of_val(&an_error));
    /// let a_boxed_error = Box::<dyn Error + Send + Sync>::from(an_error);
    /// assert!(
    ///     mem::size_of::<Box<dyn Error + Send + Sync>>() == mem::size_of_val(&a_boxed_error))
    /// ```
    fn from(err: E) -> Box<dyn Error + Send + Sync + 'a> {
        Box::new(err)
    }
}

impl From<String> for Box<dyn Error + Send + Sync> {
    /// Converts a [`String`] into a box of dyn [`Error`] + [`Send`] + [`Sync`].
    ///
    /// # Examples
    ///
    /// ```
    /// use std::error::Error;
    /// use std::mem;
    ///
    /// let a_string_error = "a string error".to_string();
    /// let a_boxed_error = Box::<dyn Error + Send + Sync>::from(a_string_error);
    /// assert!(
    ///     mem::size_of::<Box<dyn Error + Send + Sync>>() == mem::size_of_val(&a_boxed_error))
    /// ```
    #[inline]
    fn from(err: String) -> Box<dyn Error + Send + Sync> {
        struct StringError(String);

        impl Error for StringError {
            #[allow(deprecated)]
            fn description(&self) -> &str {
                &self.0
            }
        }

        impl Display for StringError {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                Display::fmt(&self.0, f)
            }
        }

        // Purposefully skip printing "StringError(..)"
        impl Debug for StringError {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                Debug::fmt(&self.0, f)
            }
        }

        Box::new(StringError(err))
    }
}

impl From<String> for Box<dyn Error> {
    /// Converts a [`String`] into a box of dyn [`Error`].
    ///
    /// # Examples
    ///
    /// ```
    /// use std::error::Error;
    /// use std::mem;
    ///
    /// let a_string_error = "a string error".to_string();
    /// let a_boxed_error = Box::<dyn Error>::from(a_string_error);
    /// assert!(mem::size_of::<Box<dyn Error>>() == mem::size_of_val(&a_boxed_error))
    /// ```
    fn from(str_err: String) -> Box<dyn Error> {
        let err1: Box<dyn Error + Send + Sync> = From::from(str_err);
        let err2: Box<dyn Error> = err1;
        err2
    }
}

impl<'a> From<&str> for Box<dyn Error + Send + Sync + 'a> {
    /// Converts a [`str`] into a box of dyn [`Error`] + [`Send`] + [`Sync`].
    ///
    /// [`str`]: prim@str
    ///
    /// # Examples
    ///
    /// ```
    /// use std::error::Error;
    /// use std::mem;
    ///
    /// let a_str_error = "a str error";
    /// let a_boxed_error = Box::<dyn Error + Send + Sync>::from(a_str_error);
    /// assert!(
    ///     mem::size_of::<Box<dyn Error + Send + Sync>>() == mem::size_of_val(&a_boxed_error))
    /// ```
    #[inline]
    fn from(err: &str) -> Box<dyn Error + Send + Sync + 'a> {
        From::from(String::from(err))
    }
}

impl From<&str> for Box<dyn Error> {
    /// Converts a [`str`] into a box of dyn [`Error`].
    ///
    /// [`str`]: prim@str
    ///
    /// # Examples
    ///
    /// ```
    /// use std::error::Error;
    /// use std::mem;
    ///
    /// let a_str_error = "a str error";
    /// let a_boxed_error = Box::<dyn Error>::from(a_str_error);
    /// assert!(mem::size_of::<Box<dyn Error>>() == mem::size_of_val(&a_boxed_error))
    /// ```
    fn from(err: &str) -> Box<dyn Error> {
        From::from(String::from(err))
    }
}

impl<'a, 'b> From<Cow<'b, str>> for Box<dyn Error + Send + Sync + 'a> {
    /// Converts a [`Cow`] into a box of dyn [`Error`] + [`Send`] + [`Sync`].
    ///
    /// # Examples
    ///
    /// ```
    /// use std::error::Error;
    /// use std::mem;
    /// use std::borrow::Cow;
    ///
    /// let a_cow_str_error = Cow::from("a str error");
    /// let a_boxed_error = Box::<dyn Error + Send + Sync>::from(a_cow_str_error);
    /// assert!(
    ///     mem::size_of::<Box<dyn Error + Send + Sync>>() == mem::size_of_val(&a_boxed_error))
    /// ```
    fn from(err: Cow<'b, str>) -> Box<dyn Error + Send + Sync + 'a> {
        From::from(String::from(err))
    }
}

impl<'a> From<Cow<'a, str>> for Box<dyn Error> {
    /// Converts a [`Cow`] into a box of dyn [`Error`].
    ///
    /// # Examples
    ///
    /// ```
    /// use std::error::Error;
    /// use std::mem;
    /// use std::borrow::Cow;
    ///
    /// let a_cow_str_error = Cow::from("a str error");
    /// let a_boxed_error = Box::<dyn Error>::from(a_cow_str_error);
    /// assert!(mem::size_of::<Box<dyn Error>>() == mem::size_of_val(&a_boxed_error))
    /// ```
    fn from(err: Cow<'a, str>) -> Box<dyn Error> {
        From::from(String::from(err))
    }
}


// #[unstable(
//     feature = "allocator_api",
//     reason = "the precise API and guarantees it provides may be tweaked.",
//     issue = "32838"
// )]
// impl Error for AllocError {}

//
// impl Error for LayoutErr {}

impl Error for str::ParseBoolError {
    #[allow(deprecated)]
    fn description(&self) -> &str {
        "failed to parse bool"
    }
}

impl Error for str::Utf8Error {
    #[allow(deprecated)]
    fn description(&self) -> &str {
        "invalid utf-8: corrupt contents"
    }
}

impl Error for num::ParseIntError {
    #[allow(deprecated)]
    fn description(&self) -> &str {
        // self.__description()
        ""
    }
}

impl Error for num::TryFromIntError {
    #[allow(deprecated)]
    fn description(&self) -> &str {
        // self.__description()
        ""
    }
}

impl Error for array::TryFromSliceError {
    #[allow(deprecated)]
    fn description(&self) -> &str {
        ""
        // self.__description()
    }
}

impl Error for num::ParseFloatError {
    #[allow(deprecated)]
    fn description(&self) -> &str {
        ""
        // self.__description()
    }
}

impl Error for string::FromUtf8Error {
    #[allow(deprecated)]
    fn description(&self) -> &str {
        "invalid utf-8"
    }
}

impl Error for string::FromUtf16Error {
    #[allow(deprecated)]
    fn description(&self) -> &str {
        "invalid utf-16"
    }
}

impl Error for Infallible {
    fn description(&self) -> &str {
        match *self {}
    }
}

impl Error for char::DecodeUtf16Error {
    #[allow(deprecated)]
    fn description(&self) -> &str {
        "unpaired surrogate found"
    }
}

impl<T: Error> Error for Box<T> {
    #[allow(deprecated, deprecated_in_future)]
    fn description(&self) -> &str {
        Error::description(&**self)
    }

    #[allow(deprecated)]
    fn cause(&self) -> Option<&dyn Error> {
        Error::cause(&**self)
    }

    fn source(&self) -> Option<&(dyn Error + 'static)> {
        Error::source(&**self)
    }
}

impl Error for fmt::Error {
    #[allow(deprecated)]
    fn description(&self) -> &str {
        "an error occurred when formatting an argument"
    }
}

impl Error for cell::BorrowError {
    #[allow(deprecated)]
    fn description(&self) -> &str {
        "already mutably borrowed"
    }
}

impl Error for cell::BorrowMutError {
    #[allow(deprecated)]
    fn description(&self) -> &str {
        "already borrowed"
    }
}

impl Error for char::CharTryFromError {
    #[allow(deprecated)]
    fn description(&self) -> &str {
        "converted integer out of range for `char`"
    }
}

impl Error for char::ParseCharError {
    #[allow(deprecated)]
    fn description(&self) -> &str {
        // self.__description()
        ""
    }
}

// impl Error for alloc::collections::TryReserveError {}

// Copied from `any.rs`.
impl dyn Error + 'static {
    /// Returns `true` if the boxed type is the same as `T`
    #[inline]
    pub fn is<T: Error + 'static>(&self) -> bool {
        // Get `TypeId` of the type this function is instantiated with.
        let t = TypeId::of::<T>();

        // Get `TypeId` of the type in the trait object.
        let boxed = self.type_id(private::Internal);

        // Compare both `TypeId`s on equality.
        t == boxed
    }

}

impl dyn Error + 'static + Send {
    /// Forwards to the method defined on the type `dyn Error`.
    #[inline]
    pub fn is<T: Error + 'static>(&self) -> bool {
        <dyn Error + 'static>::is::<T>(self)
    }
}

impl dyn Error + 'static + Send + Sync {
    /// Forwards to the method defined on the type `dyn Error`.
    #[inline]
    pub fn is<T: Error + 'static>(&self) -> bool {
        <dyn Error + 'static>::is::<T>(self)
    }

}

impl dyn Error {
    /// Returns an iterator starting with the current error and continuing with
    /// recursively calling [`Error::source`].
    ///
    /// If you want to omit the current error and only use its sources,
    /// use `skip(1)`.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(error_iter)]
    /// use std::error::Error;
    /// use std::fmt;
    ///
    /// #[derive(Debug)]
    /// struct A;
    ///
    /// #[derive(Debug)]
    /// struct B(Option<Box<dyn Error + 'static>>);
    ///
    /// impl fmt::Display for A {
    ///     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    ///         write!(f, "A")
    ///     }
    /// }
    ///
    /// impl fmt::Display for B {
    ///     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    ///         write!(f, "B")
    ///     }
    /// }
    ///
    /// impl Error for A {}
    ///
    /// impl Error for B {
    ///     fn source(&self) -> Option<&(dyn Error + 'static)> {
    ///         self.0.as_ref().map(|e| e.as_ref())
    ///     }
    /// }
    ///
    /// let b = B(Some(Box::new(A)));
    ///
    /// // let err : Box<Error> = b.into(); // or
    /// let err = &b as &(dyn Error);
    ///
    /// let mut iter = err.chain();
    ///
    /// assert_eq!("B".to_string(), iter.next().unwrap().to_string());
    /// assert_eq!("A".to_string(), iter.next().unwrap().to_string());
    /// assert!(iter.next().is_none());
    /// assert!(iter.next().is_none());
    /// ```

    #[inline]
    pub fn chain(&self) -> Chain<'_> {
        Chain { current: Some(self) }
    }
}

/// An iterator over an [`Error`] and its sources.
///
/// If you want to omit the initial error and only process
/// its sources, use `skip(1)`.

#[derive(Clone, Debug)]
pub struct Chain<'a> {
    current: Option<&'a (dyn Error + 'static)>,
}


impl<'a> Iterator for Chain<'a> {
    type Item = &'a (dyn Error + 'static);

    fn next(&mut self) -> Option<Self::Item> {
        let current = self.current;
        self.current = self.current.and_then(Error::source);
        current
    }
}

impl dyn Error + Send {
}

impl dyn Error + Send + Sync {
}
