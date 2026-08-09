INSERT INTO app.type_samples (
  statuses,
  emails,
  card,
  score,
  scores,
  amount,
  observed_at,
  nickname,
  aliases
)
VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9)
RETURNING
  id,
  statuses,
  emails,
  card,
  score,
  scores,
  amount,
  observed_at,
  nickname,
  aliases;
