package Default_Init
with Initializes => R
is
   type Result (Found : Boolean := False) is record
      case Found is
         when False => null;
         when True  => Content : Natural;
      end case;
   end record;

   --  This should be OK, since by default found = false and then the
   --  record is initialized due to having no fields.

   R : Result;
end Default_Init;
