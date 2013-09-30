with System.Storage_Elements;

package Volatiles_Illegal_5
  with SPARK_Mode
is
   pragma Elaborate_Body (Volatiles_Illegal_5);

   --  TU: 6. A constant, a discriminant or a loop parameter shall not be
   --  Volatile.
   Const_Vol : constant Integer
     with Volatile,
          Address => System.Storage_Elements.To_Address (16#A11#);

   type Vol_Int_T is new Integer with Volatile;

   Vol_Var : Vol_Int_T
     with Address => System.Storage_Elements.To_Address (16#A22#);

   --  TU: 6. A constant, a discriminant or a loop parameter shall not be
   --  Volatile.
   type Disc_Rec(D : Vol_Int_T) is record
      case D is
         when 0  => B : Boolean;
         when others => I : Integer;
      end case;
   end record;

   --  TU: 7. A non-volatile object shall not have a Volatile component.
   type Disc_Rec_2 is record
      A : Integer;
      B : Vol_Int_T;  --  Cannot have a volatile component in a non volatile
                      --  object.
   end record;
end Volatiles_Illegal_5;