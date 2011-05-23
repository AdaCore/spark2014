package Pack is

   type Disc_Rec (Disc : Boolean) is
      record
         case Disc is
            when True  => I : Integer;
            when False => B : Boolean;
         end case;
      end record;

end Pack;
