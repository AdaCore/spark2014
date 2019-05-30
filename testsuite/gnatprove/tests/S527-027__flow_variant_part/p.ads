package P is
   V : Integer := 0;                     --  variable
   type T (A, B, C : Integer) is record
      X : Integer := V;                  --  illegal
      case A is
         when 0 =>
            Y : Integer := V;            --  illegal
            case B is
               when 0 =>
                  Z : Integer := V;      --  illegal
               when others =>
                  null;
            end case;
         when others =>
            null;
      end case;
   end record;
end;
