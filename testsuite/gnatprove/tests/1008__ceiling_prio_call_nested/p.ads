package P is

   package Inner is
      protected PO
        with Priority => 1
      is
         procedure PP1
         with Global => null, Always_Terminates;
      end;
   end Inner;

end P;
