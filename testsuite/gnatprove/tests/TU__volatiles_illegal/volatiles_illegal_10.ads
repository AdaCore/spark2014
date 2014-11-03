with System.Storage_Elements;

package Volatiles_Illegal_10
  with SPARK_Mode
is
   type Vol_Int_T is new Integer with Volatile;

   --  TU: 6. A constant object (other than a formal parameter of mode
   --  **in**) shall not be effectively volatile. An effectively
   --  volatile object shall not have a discriminated part.
   type Disc_Rec(D : Vol_Int_T) is record
      case D is
         when 0  => B : Boolean;
         when others => I : Integer;
      end case;
   end record;
end Volatiles_Illegal_10;
