procedure Test_UU with SPARK_Mode is
   type R (D : Boolean := True) is record
      case D is
         when True =>
            X : Integer;
         when False =>
            Y : Float;
      end case;
   end record;

   type U is new R with Unchecked_Union;

   X : U with Relaxed_Initialization;

   type I is new Integer with Relaxed_Initialization;

   type U_2 (D : Boolean := True) is record
      case D is
         when True =>
            X : I;
         when False =>
            Y : Float;
      end case;
   end record with Unchecked_Union;

   type R_3 (D : Boolean := True) is record
      case D is
         when True =>
            X : I;
         when False =>
            Y : Float;
      end case;
   end record;

   type U_3 is new R_3 with Unchecked_Union;
begin
   null;
end Test_UU;
