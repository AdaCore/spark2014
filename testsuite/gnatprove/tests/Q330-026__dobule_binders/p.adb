package body P is

   protected body PT is
      function Prot return Boolean is
         function Identity1 (X : Boolean) return Boolean
           with Pre => True, Global => null
         is
         begin
            return X;
         end;

         function Identity2 (X : Boolean) return Boolean
           with Pre => True, Global => PT
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
