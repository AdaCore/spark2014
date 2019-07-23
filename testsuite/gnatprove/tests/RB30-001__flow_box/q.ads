package Q is

   type T (Valid : Boolean) is record
      case Valid is
         when True =>
            C : Integer;
         when False =>
            null;
      end case;
   end record;

   pragma Assert (T'(Valid => True, C => <>) = T'(Valid => True, C => <>));

end;
