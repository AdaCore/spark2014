package Update_Illegal_3
  with SPARK_Mode
is
   type Discr_Record_T (Discr : Boolean := True) is record
      A, B : Integer;
      case Discr is
         when True =>
            C : Integer;
         when others =>
            D : Integer;
      end case;
   end record;

   procedure P1 (Discr_Rec : in out Discr_Record_T);
end Update_Illegal_3;
