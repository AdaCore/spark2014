package Bar with SPARK_Mode is
   type Rec is record
      X : Integer;
      Y : Integer;
   end record;

   type RRec is record X : Integer; end record;

   function Id (R : Rec) return Rec with Import, Global => null;

   function GetX (R : Rec) return Integer is (R.X);

   procedure Baz (R : in out Rec) with
     Post => RRec ((RRec'(X => Rec'(Id (R)'Old with delta X => R.X).X) with delta X => R.X)).X = R.X;
end Bar;
