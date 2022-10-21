with Types; use Types;
with Ada.Containers; use Ada.Containers;

package Axioms with SPARK_Mode, Ghost is

   procedure Axiom_Eq_Reflexive (X : T) with
     Import,
     Global   => null,
     Annotate => (GNATprove, Always_Return),
     Post     => X = X;

   procedure Axiom_Eq_Symmetric (X, Y : T) with
     Import,
     Global   => null,
     Annotate => (GNATprove, Always_Return),
     Pre      => X = Y,
     Post     => Y = X;

   procedure Axiom_Eq_Transitive (X, Y, Z : T) with
     Import,
     Global   => null,
     Annotate => (GNATprove, Always_Return),
     Pre      => X = Y and Y = Z,
     Post     => X = Z;

   procedure Axiom_Equivalent_Reflexive (X, Y : T) with
     Import,
     Global   => null,
     Annotate => (GNATprove, Always_Return),
     Pre      => X = Y,
     Post     => Equivalent (X, Y);

   procedure Lemma_Equivalent_Reflexive (X : T) with
     Post => Equivalent (X, X);

   procedure Axiom_Equivalent_Symmetric (X, Y : T) with
     Import,
     Global   => null,
     Annotate => (GNATprove, Always_Return),
     Pre      => Equivalent (X, Y),
     Post     => Equivalent (Y, X);

   procedure Axiom_Equivalent_Transitive (X, Y, Z : T) with
     Import,
     Global   => null,
     Annotate => (GNATprove, Always_Return),
     Pre      => Equivalent (X, Y) and Equivalent (Y, Z),
     Post     => Equivalent (X, Z);

   procedure Axiom_Lt_Irreflexive (X, Y : T) with
     Import,
     Global   => null,
     Annotate => (GNATprove, Always_Return),
     Pre      => X = Y,
     Post     => not (X < Y);

   procedure Lemma_Lt_Irreflexive (X : T) with
     Post => not (X < X);

   procedure Axiom_Lt_Asymmetric (X, Y : T) with
     Import,
     Global   => null,
     Annotate => (GNATprove, Always_Return),
     Pre      => X < Y,
     Post     => not (Y < X);

   procedure Axiom_Lt_Transitive (X, Y, Z : T) with
     Import,
     Global   => null,
     Annotate => (GNATprove, Always_Return),
     Pre      => X < Y and Y < Z,
     Post     => X < Z;

   procedure Axiom_Lt_Order (X, Y, Z : T) with
     Import,
     Global   => null,
     Annotate => (GNATprove, Always_Return),
     Pre      => X < Y,
     Post     => X < Z or Z < Y;

   procedure Axiom_Hash_Equivalent (X, Y : T) with
     Import,
     Global   => null,
     Annotate => (GNATprove, Always_Return),
     Pre      => Equivalent (X, Y),
     Post     => Hash (X) = Hash (Y);

   procedure Axiom_Hash_Compatible (X : T) with
     Import,
     Global   => null,
     Annotate => (GNATprove, Always_Return),
     Post     => Hash (X) = Hash (F (X));

   procedure Axiom_Eq_Compatible (X, Y : T) with
     Import,
     Global   => null,
     Annotate => (GNATprove, Always_Return),
     Post     => Equivalent (X, Y) = Equivalent (F (X), F (Y));

   procedure Axiom_Lt_Compatible (X, Y : T) with
     Import,
     Global   => null,
     Annotate => (GNATprove, Always_Return),
     Post     => (X < Y) = (F (X) < F (Y));

end Axioms;
