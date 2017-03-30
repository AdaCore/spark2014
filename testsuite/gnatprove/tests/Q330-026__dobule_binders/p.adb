package body P is

   protected body PT is
      function Prot return Boolean is
         function Identity1 (X : Boolean) return Boolean
           with Pre => True
         is
         begin
            return X;
         end;

         function Identity2 (X : Boolean) return Boolean
           with Pre => True--, Global => PT
                           --  This global is rejected by the frontend;
                           --  probably a bug.
         is
         begin
            return X and Dummy;
         end;

      --  Start of processing for Prot

      begin
         return Identity1 (Dummy) and Identity2 (Dummy);
      end;
   end;

end;
