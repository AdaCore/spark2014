package Glob is

   package Priv is
      type T1 is private; --  there is no explicit DIC here
   private
      type T1 is record
         C : Boolean := True;
      end record;
   end Priv;

   procedure Read;

   type T2 is record
      Data  : Priv.T1;
      Valid : Boolean := False;
   end record;
   --  If flow assumes missing DIC on Data type as null, then this
   --  record type is not initialized by default; if flow generates
   --  the missing DIC, then this type is initialized by default.

end Glob;
