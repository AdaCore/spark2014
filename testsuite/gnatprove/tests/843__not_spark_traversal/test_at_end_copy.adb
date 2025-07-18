procedure Test_At_End_Copy with SPARK_Mode is

   type Holder is record
      C : aliased Integer;
   end record;

   function At_End (X : access constant Integer) return access constant Integer is (X) with
     Ghost,
     Annotate => (GNATprove, At_End_Borrow);

   function At_End (X : Holder) return Holder is (X) with
     Ghost,
     Annotate => (GNATprove, At_End_Borrow);

   function F (X : aliased in out Holder) return not null access Integer with
     Post => At_End (X).C = At_End (F'Result).all;

   function F (X : aliased in out Holder) return not null access Integer is
   begin
      return X.C'Access;
   end F;

   X : aliased Holder := (C => 1);
   B : access Integer := F (X);
   X_E : constant Holder := At_End (X) with Ghost; -- This should not be allowed or the assertion below would be provable
begin
   B.all := 3;
   pragma Assert (At_End (X) = X_E);
end;
