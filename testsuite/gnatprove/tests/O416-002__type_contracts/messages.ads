package Messages
  with SPARK_Mode
is
   type Day is new String (1 .. 10);

   type Message is record
      Sent     : Day;
      Received : Day;
   end record with
     Dynamic_Predicate => Message.Sent <= Message.Received;

   procedure Process (M : in out Message);

end Messages;
