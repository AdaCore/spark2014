pragma SPARK_Mode(On);

package union_init is
   type Intarray is array(0..2) of Integer;

   type basic_record is record
      length      : Integer := 0;
      basic_array : Intarray := (others => 0);
   end record;


   type union_test (discr : Integer := 0) is record
      case discr is
         when 0 =>
            field1 : Integer := 0;
         when 1 =>
            field2 : basic_record;
         when others =>
            field3 : Natural := 0;
      end case;
   end record;

   procedure init_union (test : out union_test);
end union_init;
