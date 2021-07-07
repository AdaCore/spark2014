procedure Bad_At_End_Borrow with SPARK_Mode is
   type Rec is record
      I, J : aliased Integer;
   end record;

   function AE (X : access constant Rec) return access constant Rec is (X) with
     Ghost,
     Annotate => (GNATprove, At_End_Borrow);

   function AE (X : access constant Integer) return access constant Integer is (X) with
     Ghost,
     Annotate => (GNATprove, At_End_Borrow);

   type Int_Acc is access Integer;
   type Rec_2 is record
      F : Int_Acc;
   end record;

   function Get_I (X : Rec_2) return access Integer is (X.F);

   X : aliased Rec := (others => 1);
begin
   declare
      Y : not null access Rec := X'Access;
      I : not null access Integer := Y.I'Access;
      procedure Bad with Import,
        Pre => AE (Y).all = (Y.all with delta I => AE (I).all);
   begin
      Bad;
   end;
end Bad_At_End_Borrow;
