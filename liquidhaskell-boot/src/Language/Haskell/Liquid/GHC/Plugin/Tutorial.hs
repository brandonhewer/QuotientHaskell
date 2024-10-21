
module Language.Haskell.Liquid.GHC.Plugin.Tutorial (

  -- * Introduction and Requirements
  -- $introduction

  -- * Your first package
  -- $firstPackage

  -- * Using GHCi
  -- $usingGHCi

  -- * Passing options
  -- $passingOptions

  -- * Providing specifications for existing packages
  -- $specForExisting

) where

{- $introduction

This tutorial describes the general approach of using LiquidHaskell using the new compiler plugin. Due
to some recent changes and improvements to the compiler plugin API (which LiquidHaskell requires) the
__minimum supported version of GHC is 8.10.1.__

-}

{- $firstPackage

Generally speaking, in order to integrate LiquidHaskell (/LH/ for brevity from now on) with your existing
(or brand new) project, we need to tell GHC that we want to __use the LH plugin__, and it can be done
by adding the @-fplugin=LiquidHaskell@ option in the @ghc-options@ of your Cabal manifest.

If we do the above, our Cabal manifest should look similar to this:

@
cabal-version: 1.12

name:           toy-package-a
version:        0.1.0.0
description:    This is a toy example.
homepage:
bug-reports:
author:         Author name here
maintainer:     example@example.com
copyright:      2019 Author name here
license:        BSD3
license-file:   LICENSE
build-type:     Simple

library
  exposed-modules:
      Toy.A
  hs-source-dirs:
      src
  build-depends:
        base
      , liquidhaskell                  -- Add this!
  default-language: Haskell2010
  ghc-options: -fplugin=LiquidHaskell  -- Add this!
@

Let's now define a very simple module called 'Toy.A':

@
module Toy.A ( notThree, one, two) where

\{\-\@ one :: {v:Int | v = 1 } \@\-\}
one :: Int
one = 1

\{\-\@ assume notThree :: {v : Nat | v != 3 } \@\-\}
notThree :: Int
notThree = 4

\{\-\@ two :: Nat \@\-\}
two :: Int
two = one + one
@

Now, if we build the package with (for example) @cabal v2-build toy-package-a@, we should see something
like this:

@
Resolving dependencies...
Build profile: -w ghc-8.10.1 -O1
In order, the following will be built (use -v for more details):
 - toy-package-a-0.1.0.0 (lib) (configuration changed)
Configuring library for toy-package-a-0.1.0.0..
Warning: The 'license-file' field refers to the file 'LICENSE' which does not
exist.
Preprocessing library for toy-package-a-0.1.0.0..
Building library for toy-package-a-0.1.0.0..

[3 of 3] Compiling Toy.A            ( src\/Toy\/A.hs, ... )

**** LIQUID: SAFE (7 constraints checked) **************************************
@

The \"SAFE\" banner here is LH's way of saying "all is well". What happens if we try to violate a
refinement? Let's find out. If change @one@ to look like this:

@
{-@ one :: {v:Int | v = 1 } @-}
one :: Int
one = 2
@

Upon next recompilation, GHC (or rather, /LH/) will bark at us:

@
Building library for toy-package-a-0.1.0.0..
[3 of 3] Compiling Toy.A            ( src\/Toy\/A.hs, ... )

**** LIQUID: UNSAFE ************************************************************

src\/Toy\/A.hs:36:1: error:
    Liquid Type Mismatch
    .
    The inferred type
      VV : {v : GHC.Types.Int | v == 2}
    .
    is not a subtype of the required type
      VV : {VV : GHC.Types.Int | VV == 1}
    .
   |
36 | one = 2
   | ^^^^^^^
@

-}

{- $passingOptions

Passing options to /LH/ is possible and works using the standard mechanism the plugin system already provides.
For example let's image we want to skip verification of our 'Toy.A' module. At this point, we have two options:

1. We can add the option directly in the module, as a \"pragma\":

    @
    \{\-\@ LIQUID "--compilespec" \@\-\}
    module Toy.A ( notThree, one, two) where
    ...
    @

2. We can add this \"globally\" (if that's really what we want), like this:

    @
    cabal-version: 1.12
    name:           toy-package-a
      ..
      default-language: Haskell2010
      ghc-options: -fplugin=LiquidHaskell -fplugin-opt=LiquidHaskell:--compilespec
    @

-}

{- $usingGHCi

Using GHCi is supported out of the box, and it will work as expected.

-}

{- $specForExisting

If you have control over the package or project you would like to annotate with /LH/ refinements, all is well.
But what about packages you don't own or maintain? Typically, one solution would be to convince the
project's maintainers to get on board and to add /LH/ annotations to the code themselves, but this might not
be so easy, for a number of reasons:

* The package you are trying to \"refine\" is not maintained anymore, or the maintainer is very difficult
  to reach;

* The package is fairly important in the Haskell ecosystem and making changes to it might not be so easy,
  especially for packages which come as part of a GHC installation (think @base@, for example).

The designed workflow in these cases is to create a __brand new package__ (that we can call an \"assumptions\" package),
which would contain the required /LH/ annotations. This is what we have done for things like @vector@ and @parallel@,
for example, by providing @liquid-vector@ and @liquid-parallel@.

There are some guidelines to drive this process:

1. Typically you want to clearly identify this package as part of the /LH ecosystem/ by using an
   appropriate prefix for your package name, something like @liquid-foo@ where @foo@ is the original
   package you are adding annotations for;

2. If you want to have Liquid Haskell load the specs automatically when finding
   an import of a module @A.B.C@, put the specs in a module named
   @A.B.C_LHAssumptions@.

3. You need to abide to a set of PVP rules, like tracking the version of the upstream package first and
   in case of changes to either the LH language or the specs in the mirror package, bump the last two
   digits of the version scheme, in a format like this:

   @liquid-\<package-name\>-A.B.C.D.X.Y@

   Where @A.B.C.D@ would be used to track the upstream package version and @X.Y@ would enumerate the
   versions of this mirror package. Bumping @X@ would signify there was a breaking change in the /LH/
   language that required a new release of this plugin, whereas bumping @Y@ would mean something changed
   in the __specs__ provided as part of this assumptions package (e.g. more refinements were added,
   bugs were fixed etc).
-}
