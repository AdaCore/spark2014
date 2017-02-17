package Types is

   type Enum is (A, B);

   type R (I : Enum) is
      record
         case I is
            when A => X : Integer;
            when B => Y : Float;
         end case;
      end record;

end Types;
