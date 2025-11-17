package P is

   type Rec (Kind : Character) is record
      case Kind is
         when 'A' =>
            X : Natural;

         when 'B' =>
            Y : Natural;
            Z : Natural;

         when others =>
            W : Natural;
      end case;
   end record;

   procedure Test_Rec (S : Rec);

end P;
