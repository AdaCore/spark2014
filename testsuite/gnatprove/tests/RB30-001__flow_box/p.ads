package P is

   type T (Valid : Boolean) is record
      case Valid is
         when True =>
            C : Integer;
         when False =>
            null;
      end case;
   end record;

   procedure Get (X : Integer; Y : out T) with Pre => not Y'Constrained;

end;
