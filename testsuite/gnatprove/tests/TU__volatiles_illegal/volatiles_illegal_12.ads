with System.Storage_Elements;

package Volatiles_Illegal_10
  with SPARK_Mode
is
   type Vol_Int_T is new Integer with Volatile;

   --  TU: 6. A constant, a discriminant or a loop parameter shall not be
   --  Volatile.
   type Disc_Rec(D : Vol_Int_T) is record
      case D is
         when 0  => B : Boolean;
         when others => I : Integer;
      end case;
   end record;
end Volatiles_Illegal_10;
