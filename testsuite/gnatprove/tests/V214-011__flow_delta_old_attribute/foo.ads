package Foo with SPARK_Mode is
   type Rec is record
      X : Integer;
      Y : Integer;
   end record;

   type RRec is new Rec;

   function GetX (R : Rec) return Integer is (R.X);

   procedure Bar (R : in out Rec) with
     Post => RRec'(RRec (R'Old) with delta X => R.X).X = R.X;
end Foo;
