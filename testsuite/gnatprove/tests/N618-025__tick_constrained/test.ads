package Test is

   type Discr_Rec_T (D : Integer := 0) is record
      X : Integer;
      case D is
         when 1 =>
            Y : Integer;
         when 2 =>
            Z : Integer;
         when others =>
            null;
      end case;
   end record;

   type My_Range is range 1 .. 10;

   type Arr_Of_Discr_T is array (My_Range) of Discr_Rec_T;

   procedure Foo (Index : My_Range;
                  Arr   : in out Arr_Of_Discr_T)
     with Pre => not Arr (Index)'Constrained;
end Test;
