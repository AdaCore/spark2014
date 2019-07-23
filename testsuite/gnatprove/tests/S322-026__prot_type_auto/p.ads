package P is
   protected type PT is
      procedure P;
   private
      X : access Integer := null;
   end;
end;
