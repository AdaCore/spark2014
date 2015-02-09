package Parent.Pub_Child is
   type Extended_T is new Root_T with private;

   overriding procedure Initialize (E : out Extended_T);
private
   type Extended_T is new Root_T with record
      Y : Integer;
   end record;
end Parent.Pub_Child;
