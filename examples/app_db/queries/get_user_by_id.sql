SELECT
  u.id,
  u.organization_id,
  u.email,
  u.status,
  u.display_name,
  u.created_at
FROM app.users AS u
WHERE u.id = $1;
