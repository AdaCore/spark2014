package PrePost is
   procedure F (X : Integer)
      with Pre => (X > 0),
           Post => (X < 0);
end PrePost;
