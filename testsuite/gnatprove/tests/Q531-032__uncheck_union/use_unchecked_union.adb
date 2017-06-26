pragma SPARK_Mode(On);

package body use_unchecked_union is

   --2 proc doing the same assignations to an unchecked union,
   --the first using the discriminant, the second without


   procedure doStuff (output : out myUnion;
                      num : in Integer)
   is
   begin
      case (num) is
         when 0 =>
            output := (discr => 0, record1 => (1, (1,2,3)));
         when 1 =>
            output := (discr => 1, record2 => (1, (1,2,3,4)));
         when others =>
            output := (discr => 1, record2 => (0, (0,0,0,0)));
      end case;
   end doStuff;
   --discriminant check might fail



   procedure doStuff2 (output : out myUnion;
                       num : in Integer)
   is
   begin
      case (num) is
         when 0 =>
            output.record1.field1 := 1;
            output.record1.field2 := (1,2,3);
         when 1 =>
            output.record2.field1 := 1;
            output.record2.field2 := (1,2,3,4);
         when others =>
            output.record2.field1 := 0;
            output.record2.field2 := (others =>0);
      end case;
   end doStuff2;
   -- input value might be used in doStuff2

end use_unchecked_union;
