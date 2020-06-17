procedure Test_Pledge with SPARK_Mode is
   type Int_Acc is access Integer;

   function Pledge (Borrower : access constant Integer; Prop : Boolean) return Boolean is
     (Prop)
   with Ghost,
     Annotate => (GNATprove, Pledge);

   function Id_OK (X : Int_Acc) return access Integer is (X) with
     Post => Pledge (Id_OK'Result, True),
     Contract_Cases =>
       (X = null => Pledge (Id_OK'Result, True),
        X /= null and then X.all = 1 => Pledge (Id_OK'Result, True),
        others => Pledge (Id_OK'Result, True));

   X : Int_Acc;
   Y : access Integer := X;

   function Read_Y_OK return Integer is (Y.all) with
     Pre => Pledge (Y, True);

   function Read_Y_Bad return Integer is (Y.all) with
     Contract_Cases =>
       (Pledge (Y, True) => True,
        others => Read_Y_Bad'Result = 1);
begin
   --  OK
   pragma Assert (Pledge (Y, True) or else Pledge (Y, X = null));
   pragma Assert (Pledge (Y, True) and then Pledge (Y, X = null));
   pragma Assert (Pledge (Y, True) and Pledge (Y, X = null));
   pragma Assert (Pledge (Y, True) or Pledge (Y, X = null));
   pragma Assert (if X = null then Pledge (Y, True) elsif X.all = 1 then Pledge (Y, True) else Pledge (Y, X = null));
   pragma Assert (case X = null is when True => Pledge (Y, True), when False => Pledge (Y, X = null));

   --  Bad
   pragma Assert (Pledge (Y, True) = (X = null));
   pragma Assert (if Pledge (Y, True) then True else False);
   pragma Assert (if X = null then True elsif Pledge (Y, True) then False else True);
   pragma Assert (case Pledge (Y, True) is when True => True, when False => X = null);
end Test_Pledge;
