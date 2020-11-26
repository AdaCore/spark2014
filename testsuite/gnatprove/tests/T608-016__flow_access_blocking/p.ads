package P is
   protected type PT is
      entry E (Callback : not null access procedure);
   end;
end;
