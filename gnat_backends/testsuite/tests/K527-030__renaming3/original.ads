function Original (X : Boolean) return Boolean with
  Post => Original'Result = not X;
