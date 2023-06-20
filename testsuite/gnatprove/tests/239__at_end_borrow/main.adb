procedure Main with SPARK_Mode is
   type Int_Acc is not null access Integer;
   type R is record
      F, G : Int_Acc;
   end record with Predicate => F.all < G.all;

   function A (X : access constant R) return access constant R is (X) with
     Ghost,
     Annotate => (GNATprove, At_End_Borrow);

   function Test (X : R) return Boolean is (X.F.all < X.G.all) with
     Post => Test'Result;

   procedure P (X : not null access R) is
      Y : access R := X;
      B : access Integer := Y.F;
      C : constant Integer := B.all;
   begin
      B.all := Y.G.all;
      pragma Assert (Test (A (X).all));  --  Error, Y is borrowed
      B.all := C;
   end P;

   procedure P2 (X : not null access R) is
      Y : access R := X;
      I : Int_Acc := Y.F;
      C : constant Integer := I.all;
   begin
      I.all := Y.G.all;
      pragma Assert (Test (A (X).all)); --  Error, Y is moved
      I.all := C;
      Y.F := I;
   end P2;

   X : aliased R := (new Integer'(1), new Integer'(2));
   Y : access R := X'Access;
begin
   P2 (Y);
end Main;
