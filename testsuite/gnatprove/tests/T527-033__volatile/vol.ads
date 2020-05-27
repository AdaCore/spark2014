package Vol is
   type T is new Integer with Volatile, Async_Readers;

   procedure P (X : in out T) with
     Pre  => X > 0,
     Post => X < 0;

end Vol;
