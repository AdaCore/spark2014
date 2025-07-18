procedure Test_Proof with SPARK_Mode is

   type Holder is record
      A : Integer;
      C : aliased Integer;
   end record;

   type Int_Acc is access Integer;

   type Holder_2 is record
      A : Integer;
      C : not null Int_Acc;
   end record;

   function At_End (X : access constant Integer) return access constant Integer is (X) with
     Ghost,
     Annotate => (GNATprove, At_End_Borrow);

   function At_End (X : Holder) return Holder is (X) with
     Ghost,
     Annotate => (GNATprove, At_End_Borrow);

   function F (X : aliased in out Holder) return not null access Integer with
     Post => At_End (X).A = X.A and At_End (X).C = At_End (F'Result).all;

   function F (X : aliased in out Holder) return not null access Integer is
   begin
      return X.C'Access;
   end F;

   procedure Bad_Call_F is
      X : aliased Holder := (1, 2);
   begin
      declare
         B : access Integer := F (X);
      begin
         B.all := 3;
      end;
      pragma Assert (X.C = 2); -- @ASSERT:FAIL
   end Bad_Call_F;

   function At_End (X : Holder_2) return Holder_2 is (X) with
     Ghost,
     Annotate => (GNATprove, At_End_Borrow);

   function G (X : Holder_2) return not null access Integer with
     Post => At_End (X).A = X.A and At_End (X).C.all = At_End (G'Result).all;

   function G (X : Holder_2) return not null access Integer is
   begin
      return X.C;
   end G;

   procedure Bad_Call_G is
      X : aliased Holder_2 := (1, new Integer'(2));
   begin
      declare
         B : access Integer := G (X);
      begin
         B.all := 3;
      end;
      pragma Assert (X.C.all = 2); -- @ASSERT:FAIL
   end Bad_Call_G;

   X : aliased Holder := (1, 2);
   Y : Holder_2 := (1, new Integer'(2));
begin
   declare
      B : access Integer := F (X);
   begin
      B.all := 3;
   end;
   pragma Assert (X = (1, 3));

   declare
      B : access Integer := G (Y);
   begin
      B.all := 3;
   end;
   pragma Assert (Y.A = 1 and Y.C.all = 3);
end;
