with Ext; use Ext;

procedure Main with SPARK_Mode is

   procedure Prove_Refl (X : Integer) with
     Global => null,
     Post => Equivalent (X, X);

   procedure Prove_Refl (X : Integer) is null;

   procedure Prove_Symmetric (X, Y : Integer) with
     Global => null,
     Post => Equivalent (X, Y) = Equivalent (Y, X);

   procedure Prove_Symmetric (X, Y : Integer) is null;

   procedure Prove_Transitive (X, Y, Z : Integer) with
     Global => null,
     Post => (if Equivalent (X, Y) and Equivalent (Y, Z) then Equivalent (X, Z));

   procedure Prove_Transitive (X, Y, Z : Integer) is null;

begin
   null;
end Main;
