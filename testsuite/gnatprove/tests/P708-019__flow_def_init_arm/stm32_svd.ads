package STM32_SVD is

   type R1
     (As_Array : Boolean := False)
   is record
      case As_Array is
         when False =>
            null;
         when True =>
            Arr : Integer;
      end case;
   end record;

   type R2 is record
      C : R1 := (As_Array => False);
   end record;

   X : R2;

end STM32_SVD;
