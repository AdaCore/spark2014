with System.Storage_Elements;

package Volatiles_Illegal_10
  with SPARK_Mode
is
   type Vol_Int_T is new Integer with Volatile;

   --  TU: 5. An effectively volatile type other than a protected type
   --  shall not have a discriminated part.
   type Disc_Rec(D : Vol_Int_T) is record
      case D is
         when 0  => B : Boolean;
         when others => I : Integer;
      end case;
   end record;
end Volatiles_Illegal_10;
