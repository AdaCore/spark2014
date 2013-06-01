package Pkg is

   type Parent (N : Integer := 0) is limited private;

   function Equal (X, Y : Parent) return Boolean;

private

   type Parent (N : Integer := 0) is
     record
        I : Integer := 2;

        case N is
           when 2 =>
              J : Integer := 2;
           when others =>
              null;
        end case;
     end record;
end pkg;
