package Derivation_With_Discr with SPARK_Mode is
   type Root (B : Boolean) is tagged record
      case B is
         when True  => F1 : Integer;
         when False => null;
      end case;
   end record;

   type Child (B : Boolean) is new Root (B) with record
      case B is
         when True  => null;
         when False => F3 : Integer;
      end case;
   end record;
end Derivation_With_Discr;
