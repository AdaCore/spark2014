package P is

   protected type PT is
      entry Dummy;
      procedure Proc;
      function Func return Boolean;
      function Func2 return Boolean;
   private
      X : Boolean := True;
   end;

   procedure Call;

end;
