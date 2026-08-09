INSERT INTO app.users (
  organization_id,
  email,
  status,
  display_name
)
VALUES ($1, $2, $3, $4);
