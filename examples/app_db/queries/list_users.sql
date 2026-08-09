SELECT
  u.id,
  u.organization_id,
  u.email,
  u.status,
  u.display_name,
  u.created_at
FROM app.users AS u
WHERE $1::app.user_status IS NULL OR u.status = $1
ORDER BY u.id;
