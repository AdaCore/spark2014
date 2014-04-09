package Discr with
  SPARK_Mode
is
   type R (J : Integer) is record
      case J is
         when Positive =>
            K : Integer;
         when others =>
            null;
      end case;
   end record;

   procedure P;

end Discr;
