package Storage with SPARK_Mode is

   type Int_Ptr is access Integer;

   type Weak_Int_Ptr (Valid : Boolean := False) is record
      case Valid is
         when False => null;
         when True  => Ptr : Int_Ptr;
      end case;
   end record;

   function New_Integer (N : Integer) return Weak_Int_Ptr
     with Post => (if New_Integer'Result.Valid then New_Integer'Result.Ptr /= null);

   procedure Free (P : in out Weak_Int_Ptr)
     with
       Pre  => not P'Constrained,
       Post => P.Valid = False;

end Storage;
