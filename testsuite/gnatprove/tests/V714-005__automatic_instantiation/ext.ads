package Ext with SPARK_Mode,
  Annotate => (GNATprove, Always_Return)
is

   function Equivalent (X, Y : Integer) return Boolean with
     Global => null;

   procedure Lemma_Reflexive (X : Integer) with
     Ghost,
     Global => null,
     Annotate => (GNATprove, Automatic_Instantiation),
     Post => Equivalent (X, X);

   procedure Lemma_Symmetric (X, Y : Integer) with
     Ghost,
     Global => null,
     Annotate => (GNATprove, Automatic_Instantiation),
     Pre  => Equivalent (X, Y),
     Post => Equivalent (Y, X);

   procedure Lemma_Transitive (X, Y, Z : Integer) with
     Ghost,
     Global => null,
     Annotate => (GNATprove, Automatic_Instantiation),
     Pre  => Equivalent (X, Y) and Equivalent (Y, Z),
     Post => Equivalent (X, Z);

end Ext;
