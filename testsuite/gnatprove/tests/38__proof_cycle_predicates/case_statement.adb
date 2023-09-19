procedure Case_Statement with SPARK_Mode is
   type T is record A : Integer; end record;

   function F (V : T) return Boolean with Pre => True, Post => False;

   subtype R is T with Predicate => F (R);

   function F (V : T) return Boolean
   is
   begin
      case R (V).A is
         when 1 => return True;
         when others => return False;
      end case;
   end F;

begin
   null;
end;
