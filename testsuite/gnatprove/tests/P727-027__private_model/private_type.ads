package Private_Type with SPARK_Mode => On is
   type Root is tagged private;

   function Is_Valid (R : Root) return Boolean;

   function F (R : Root) return Natural with
     Pre'Class => Is_Valid (R);
   function G (R : Root) return Natural is (F (R)); --@PRECONDITION:FAIL

private
   pragma SPARK_Mode (Off);
   type Bad is access all Integer;
   type Root is tagged record
      F : Bad;
   end record;

   function Is_Valid (R : Root) return Boolean is (True);

   function F (R : Root) return Natural is (0);
end Private_Type;
