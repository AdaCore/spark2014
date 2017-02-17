package Frame is
   type Index is new Integer range 1 .. 10;
   type Ar is array (Index) of Natural;
   type Rec is record
      C1 : Natural;
      C2 : Natural;
   end record;
   type Arrec is array (Index) of Rec;

   procedure Threshold_Ar (A : in out Ar) with
     Post => (for all J in Index => A(J) =
                (if A'Old(J) > 10 then 10 else A'Old(J)));

   procedure Copy_Rec (A : in out Arrec) with
     Post => (for all J in Index => A(J).C1 = A'Old(J).C2);

end Frame;
