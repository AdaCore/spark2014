package P is

   -- Async_Writers

   V : Integer with Volatile, Async_Writers;

   procedure P
   with
     Global => (Input => V);

   function F return Integer
   with
     Global => (Input => V),
     Side_Effects;

   -- Effective_Reads

   V2 : Integer with Volatile, Async_Writers, Effective_Reads;

   procedure P2
   with
     Global => (Input => V2);

   function F2 return Integer
   with
     Global => (Input => V2),
     Side_Effects;

end P;
