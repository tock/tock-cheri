// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Google LLC 2024.

/// Macro to create an alias for a number of traits, with automatically propagated bounds on their
/// associated types. Works with generics, const generics, does not (yet) work for GATS.
///
/// Usage:
/// ```text
/// misc::trait_alias! {
///     [vis] trait TheTrait = SuperTrait1, SuperTrait2, SuperTrait3, ...,
///         as where (SuperTraitX:::AssociatedType as NewName : Bound1 | Bound2)*
///         where [other bounds]
/// ```
/// Either of the "as where" or "where" clauses can be skipped.
/// Don't put bounds in the definition of TheTrait, put them in the [other bounds].
///
/// If you have a bound T : TheTrait, all the "as where" bounds are automatically propagated
///
/// Also, put any ?Trait bounds on associated types AT THE END. Parsing is hard.
///
/// Note the triple ":::" rather than "::" in as the _last_ path separator in the "as where" block.
///
/// Note a slightly different syntax is required for parameters of TheTrait. Instead of:
///     TheTrait<'a, 'b, const X : u8, T, const Y : bool>
/// write
///     TheTrait<'a, 'b, T ; const X : u8, const Y : bool>
///
/// The rules are: lifetimes first, followed by types, followed by a semicolon (not a comma),
/// followed by the consts.
///
/// Example, a trait for anything that be converted to and from a u8:
/// ```
/// misc::trait_alias!(
///     pub trait ConvertU8 = Into<u8>, From<u8>
/// );
/// ```
///
/// Example, a trait for any iterator where the `Item : Into<X>`:
/// ```
/// misc::trait_alias!(
///     pub trait IntoXIterator<X> = Iterator as where Iterator:::Item as IntoItem : Into<X>
/// );
/// ```
///
#[macro_export]
macro_rules! trait_alias {
    // Do the work
    ($(#[$attr:meta])* $vis:vis trait $TraitAlias : ident $(<$($t:tt),* $(; $(const $n : tt : $ty : tt),*)?>)? = $Super1 : path $(, $Super : path)*
            $(as where $($SP : ident $(:: $SPS : ident)* $(<$($($SLife : lifetime)? $($SIdent : path)?),*>)? ::: $AT : ident as $NAT : ident : $ATB1 : path $(| $ATBs : path)* $(| ? $Sized: path)? ),*)?
            $(where $($other : tt)*)?
    ) =>
    (
        // First declare the trait with appropriate supertraits
        $(#[$attr])* $vis trait $TraitAlias $(<$($t),* $(, $(const $n : $ty),*)?>)? : $Super1 $(+ $Super)* where
                // Then add in bounds that bound the new traits associated types to be the same as the supertraits
                $($(Self : $SP $(:: $SPS)* <$($($($SIdent)? $($SLife)?),* ,)? $AT = Self::$NAT>,)*)? $($($other)*)? {
            // Then declare the new associated types that have the required bounds
            $($(type $NAT : $ATB1 $(+ $ATBs)* $(+ ? $Sized)?;)*)?
        }
        // Then provide a blanket implementation
        impl<$($($t),* $(, $(const $n : $ty),*)?,)?
            TTT : ?Sized + $Super1 $(+ $Super)*> $TraitAlias $(<$($t),* $(, $($n),*)?>)? for TTT
                where $($(<Self as $SP $(:: $SPS)*$(<$($($SIdent)? $($SLife)?),*>)?>::$AT : $ATB1 $(+ $ATBs)*,)* )? $($($other)*)?
        {
            // Set the new associated type to the supertrait's associated type
            $($(type $NAT = <Self as $SP $(:: $SPS)*$(<$($($SIdent)? $($SLife)?),*>)?>::$AT ;)*)?
        }
    );
}

#[cfg(test)]
mod tests {

    // This is how we might normally specify a bound. In this instance, we are saying that
    // we are being passed some collection of type T that can be converted into an iterator
    // where the items support trivial conversion to an i32. Such a bound is what would be
    // required to sum a collection.
    //
    // This is already pretty complicated, but gets worse if we need dozens of traits.
    // Any other item (e.g. helper function) that needs 'T also needs to copy and paste all of
    // these bounds around.
    fn sum_of<NumItem: Into<i32>, T: IntoIterator<Item = NumItem>>(collection: T) -> i32 {
        let mut sum: i32 = 0;
        for val in collection {
            sum += val.into();
        }
        sum
    }

    // Instead we can use the alias. This only requires stating the bounds once:
    // "NumberIterator is an IntoIterator where the IntoIterator:::Item (call that NumItem) can
    // be converted into an i32"
    trait_alias!(
        pub trait NumIterator = IntoIterator as where IntoIterator:::Item as NumItem : Into<i32>
    );

    // Now using that trait (NumIterator) results in much cleaner code
    fn sum_of2<T: NumIterator>(collection: T) -> i32 {
        let mut sum: i32 = 0;
        for val in collection {
            sum += val.into();
        }
        sum
    }

    #[test]
    fn test_normal() {
        assert_eq!(sum_of([0u8, 1u8, 2u8, 3u8]), 6i32);
        assert_eq!(sum_of([-1i32, 777i32, 0i32, -1000i32]), -224i32);
    }

    // Note, we never said that [u8;4] or [i32;4] (the two types used) supported NumIterator.
    // It was implemented automatically because they met the bounds.

    #[test]
    fn test_with_alias() {
        assert_eq!(sum_of2([0u8, 1u8, 2u8, 3u8]), 6i32);
        assert_eq!(sum_of2([-1i32, 777i32, 0i32, -1000i32]), -224i32);
    }

    /*
     Note, the alias above will expand to:

         pub trait NumIterator: IntoIterator where Self : IntoIterator<Item=Self::NumItem>, {
             type NumItem: Into<i32>;
         }
         impl<TTT: ?Sized + IntoIterator> NumIterator for TTT
             where <Self as IntoIterator>::Item: Into<i32>, {
             type NumItem = <Self as IntoIterator>::Item;
         }

     The first item declares a new trait to be an alias. The second implements that trait for any
     types that satisfy the bounds. Note the trick with the associated type NumItem. Only
     super-trait bounds are implicitly propagated.

         One would naively try simply the NumIterator trait by writing
             pub trait NumIterator: IntoIterator where
                 Self : IntoIterator,
                 <Self as IntoIterator>::Item : Into<i32>

     However, <Self as IntoIterator>::Item : Into<i32> does not count as a super-trait as it is
     not a bound on Self. Self : IntoIterator<Item=Self::NumItem> is a bound on self, and then
     the desired bound can be put (as a super-trait) on the associated type:

         type NumItem: Into<i32>;
    */
}
