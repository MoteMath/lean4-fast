inductive BadPos where
  | mk : (BadPos → False) → BadPos
